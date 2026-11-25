---
name: proof-scaling
description: >-
  Use when proving `Expected.claim` in Anneal Lean modules, diagnosing Lean RSS
  or heartbeat timeouts, choosing `Model + DomainProof` vs `MirRefines`, or
  authoring Pass-1 `Anneal.*` lemmas under TrustedBoundary. Not for CLI basics
  (use cargo-anneal) or changing specs (use spec-authoring).
---

# Scale Anneal Lean proofs

Use this skill once `Spec.lean` / `Spec.*` is frozen (`spec-authoring`) and
direct `execProg` simplification stalls, blows memory, or hits kernel reduction
limits. Never weaken `Specs.safety` or `Specs.property` to force a proof
through.

## Step 1: Pre-flight environment and MIR support check

Before decomposing a proof, verify the toolchain actually captures the target:

1. Run `cargo anneal verify ... --artifacts <dir>` once and inspect
   `capture/capture.json` (`selected`, `program`) and `generated/Expected.lean`.
   If `unsupported` or `compiler_failed` appears, stop and report the exact
   unsupported Rust construct rather than refactoring blindly.
2. Respect host memory budgets: prefer interactive Lean 4 LSP queries (your
   editor or host `lake serve` LSP client) over repeated cold `lake env lean`
   runs, and do not launch parallel unbounded `lean` builds. In a
   `google/zerocopy` checkout, wrap CLI `lean` / `lake` / `cargo` invocations
   in `anneal/ci/anneal-lean-run`; outside a
   `google/zerocopy` checkout, pass `--lean-memory-mb <MB>` to `cargo anneal`
   or wrap CLI `lake` / `lean` builds in an OS cgroup memory cap. On delegated
   `systemd --user` Linux hosts, `ci/anneal-lean-run` reconciles
   `anneal-workloads.slice` in the user manager's `UnitPath` (`MemoryMax`,
   `MemoryHigh` at 94%, `MemorySwapMax=0`, `ManagedOOMMemoryPressure=kill` at
   40% PSI, reloading `systemd --user` on change) and enforces a scope
   `MemoryMax` / `MemorySwapMax=0` cap (`--memory-max-mb <MB>` overrides that
   `MemoryMax` and derived `lean -M`, clamped to the slice ceiling on
   cgroup-capped hosts unless `--unsafe-ignore-cgroup` is passed). Without an
   active Linux user `systemd` scope (including non-systemd Linux and macOS),
   `ci/anneal-lean-run` enforces **no** OS memory cap (`--memory-max-mb <MB>`
   only sets Lean's `-M` allocator flag for direct `lean` and `lake env lean`,
   not `lake build` or `cargo`). Separately,
   `cargo anneal verify --lean-memory-mb <MB>` sets `-M` on `cargo-anneal`'s
   internal Lean runs (subject to its mode floors) regardless of `systemd`.
3. Diagnose **Day-2 Rust bugs** first (`cargo-anneal` Step 0): if
   `Expected.lean` reveals a missing guard or bad branch in Rust, fix Rust or
   escalate the spec mismatch before tuning tactics.

## Step 2: Choose the right proof architecture

Pick the smallest decomposition matching the code pattern:

- **`Model + DomainProof` (pure/arithmetic/bitwise code):** Separate a clean
  pure Lean model `M` from MIR execution: prove `MirRefinesModel` (the
  captured MIR returns `M x` without UB/divergence) once via WP/PureLift, then
  prove `Spec (M x)` purely mathematically over `M` (`DomainProof`).
- **`Scalar == unsafe SIMD` (optimized/SIMD code):** Prove equivalence (or
  refinement) between the `unsafe`/vectorized MIR and a simple scalar reference
  model, rather than rewriting production Rust into slow "verifiable" code.
- **Keep `Expected.lean` untouched:** Never bypass `Expected.claim` or smuggle
  axioms/tactics into `Spec.*`. If `PureLift` / `MirWp` fails to discharge an
  inner block cleanly, refine invariants on clean boundary sub-lemmas.

## Step 3: Certificate-first and 6 algebraic representation shifts

Reach first for bundled `Anneal.*` certificate and lemma libraries listed in
`theory/bundle-manifest.json`, then apply structural representation shifts:

**Bundled cert & lemma modules (`theory/bundle-manifest.json`):**
<!-- pass1-bundled-modules:begin -->
- Zero-manual-WP MIR abstract-interpretation PCC (`AutoProve`, unsigned &
  signed `i8`..`i128`/`isize`, `bool`, `unit`, Bourdoncle cutpoints):
  `Anneal.AiPcc`, `Anneal.AiPcc.MirPcc`, `Anneal.AiPcc.MirBridge`,
  `Anneal.AiPcc.MirTransfer`, `Anneal.AiPcc.ReducedProduct`,
  `Anneal.AiPcc.Tnum`, `Anneal.AiPcc.WrappedInterval`, `Anneal.AiPcc.BitArith`
- Linear arithmetic Farkas certificates (replaces `omega` in Pass 1):
  `Anneal.LinearArith`
- Bitvector/SAT LRAT certificates and linear `BitVec` offset normalization
  (replaces `bv_decide` in Pass 1): `Anneal.BitTrieLrat`, `Anneal.BitVec`,
  `Anneal.BitVecArith`, `Anneal.PureLift.BvLin`
- Classical law-of-excluded-middle & core `Init` helpers (replaces `by_cases`
  in Pass 1): `Anneal.ClassicalEm`, `Anneal.InitLemmas`, `Anneal.NatBitwise`
- MIR WP, step cores, symbolic execution, and envelope soundness:
  `Anneal.MirWp`, `Anneal.MirWp.Core`, `Anneal.MirWp.Execution`,
  `Anneal.MirWp.Reflection`, `Anneal.MirWp.Scalars`, `Anneal.MirWp.V2Memory`,
  `Anneal.Wp`, `Anneal.Scalar`, `Anneal.MirTotal.Ops`,
  `Anneal.MirTotal.StepCore`, `Anneal.MirSymExec`, `Anneal.MirSymExec.Bits`,
  `Anneal.Framework`, `Anneal.Framework.StepWp`
- Loop invariants, byte/chunk layouts, forcing, `whnf`/rewrite firewalls, path
  trees, and SCC sharding: `Anneal.LoopInv`, `Anneal.LeBytes`,
  `Anneal.ListChunks`, `Anneal.SpineForce`, `Anneal.Firewall`, `Anneal.PTree`,
  `Anneal.SccSharding`, `Anneal.SccSharding.BinChunkTree`,
  `Anneal.SccSharding.InterprocCallModel`
<!-- pass1-bundled-modules:end -->

Note: `Anneal.MirTotal.Ops`, `Anneal.MirTotal.StepCore`, and
`Anneal.PureLift.BvLin` are bundled above, while repo-local
`anneal/theory/Anneal/PureLift.lean`, `Simd.lean`, `Core.lean`, and the rest of
`MirTotal` and `PureLift` remain in-tree only; `theory/bundle-manifest.json`
governs which `Anneal.*` modules `cargo anneal verify` bundles into standalone
target proofs.

**Kernel-recursion & `whnf` guardrails (avoid `#4292` / `#4295` traps):**
- **Use `Anneal.AiPcc.MirPcc` (`AutoProve`) first for acyclic scalar/signed
  safety:** `AutoProve.bodyVerified_of_autoVerifyAcyclic rfl rfl rfl` discharges
  `BodyVerified` for unsigned/signed integer, `bool`, and `unit` bodies with
  zero manual WP stepping. For loops,
  `AutoProve.bodyVerified_of_autoVerifyCutpoints` verifies caller-supplied
  Bourdoncle cutpoint `MirAbsEnv` invariants in one pass.
- **Abstract-modulus `N` for signed casts & `BitVec 128` arithmetic:** Never
  unfold `Int.subNatNat (2^128) k` or concrete `2^64`/`2^128` numerals inside
  kernel `whnf` (Lean's C++ kernel hits `(kernel) deep recursion detected`).
  Rewrite via `Anneal.MirWp.Scalars`: `evalIntToIntCast_signed_of_nonneg`,
  `evalIntToIntCast_signed_of_neg`, `evalIntToIntCast_signed_same_width`,
  `decodeScalar_signed_of_lt_half`, `decodeScalar_signed_of_ge_half`,
  `truncateScalar_unsigned_eq`, `truncateScalar_signed_eq`, and
  `evalBinOp_{bitAnd,bitOr,bitXor,shl_unsigned,shr_unsigned}_eq`,
  `evalBinOp_{add_unsigned,cmp}_eq`.
- **Flat entry locals:** On bodies with many locals or storage annotations,
  precompute `entryLocalsTail body` once into a concrete
  `tail : List LocalSlot` with `hTail : entryLocalsTail body = tail := rfl`,
  rewrite `initLocalsLoop body args 0 body.locals` to
  `entryLocals body args tail` via
  `initLocalsLoop_eq_entryLocals hValid (by decide) hTail`, and pass that
  equality to `Anneal.MirWp.safe_of_entryLocals` / `returns_of_entryLocals` /
  `executes_of_entryLocals` instead of repeatedly unfolding `initLocalsLoop` /
  `hasStorageAnnotation`:

  ```lean
  -- Replace placeholders (`[...]`, `hSafeFromEntryLocals`) for your `body`:
  private def myTail : List LocalSlot := [...] -- concrete `entryLocalsTail`
  private theorem myTail_eq : entryLocalsTail body = myTail := rfl
  -- In the proof (`hValid : ValidEntryArgs body args`):
  have hLoc := initLocalsLoop_eq_entryLocals hValid (by decide) myTail_eq
  exact safe_of_entryLocals hLoc hSafeFromEntryLocals -- placeholder proof
  ```
- **Beware `zetaHave` & dead-branch `Decidable` traps:** Do not leave unused
  `have` bindings carrying large concrete expressions in scope across `rfl` /
  `decide` / `dsimp`, and do not reduce `if h : P then ... else ...` on
  symbolic `2^64`/`2^128` inequalities without first discharging the branch via
  `ite_prop_true` / `ite_prop_false` or `Anneal.InitLemmas` (`nat_mod_*`,
  `nat_div_*`, `int_ofNat_*`, `int_subNatNat_*`, `bool_*`).

**6 algebraic representation shifts (when elaboration or `whnf` explodes):**
1. **Import `prelude` + targeted `Init.*` (`~152 MiB` vs `~473 MiB`):** Pinned
   `cargo anneal verify` and `anneal/theory/` reject monolithic `import Init`
   fail-closed; import `prelude` plus only the specific pinned `Init.Data.*`
   modules (`foundation-lock.json` in `anneal/theory/`, plus
   `library-lock.json` in pinned `cargo anneal verify`).
2. **Defunctionalize closures and higher-order combinators:** Replace captured
   `fun` closures inside proof-carrying states with small inductive tags + an
   explicit `eval` function so kernel unification never reduces huge lambda
   terms.
3. **Zero-`Prop`-arg `@[irreducible]` barriers + flat-tuple `casesOn`:** Wrap
   large sub-expressions behind `@[irreducible]` definitions taking data args
   only (no `Prop` fields hiding proofs inside data terms), and destructure flat
   product tuples with `casesOn` rather than chained `.1`/`.2` projections.
4. **Logarithmic lookup & chunked lists:** Replace linear `List` indexing /
   deeply nested updates with `Anneal.PTree` (path trees) or
   `Anneal.ListChunks`.
5. **Control reduction eagerly:** Use `Anneal.SpineForce` to force spine shapes
   before `rw`/`simp` instead of letting `whnf` unfold deep bitvectors/states.
6. **Lift pure regions first:** Factor pure computation with `Anneal.MirWp`,
   `Anneal.LoopInv`, and `Anneal.BitVec` (and `PureLift` in `theory/`) before
   reasoned arithmetic/bitvector certs.

## Step 4: Pass-1 `TrustedBoundary` rules (for `anneal/theory/` work)

Target `proof` modules (`TargetRole::Proof`) import bundled `Anneal.*` modules
to prove `Expected.claim`. When authoring Pass-1 libraries under
`anneal/theory/` or `anneal/correspondence/` (`SourceRole.theory`),
`TrustedBoundary.lean` enforces:
- Imports: `prelude` + foundation-pinned `Init.*`
  (`trusted/lean/foundation-lock.json`) + `Trusted.*` + `theory/` modules in
  `anneal/theory/` (`anneal/correspondence/` also admits sysroot foundation
  `Init.*`/`Std.*`/`Lean.*`, vendored `lean-miri`, and sibling
  `correspondence/` modules); axioms strictly in
  `[propext, Quot.sound, Classical.choice]`; zero `._unsafe_rec`.
- Forbidden tactics/items: `omega`, `bv_decide`, `by_cases`, `native_decide`,
  `decide!`, `rfl'`, `sorry`, `run_tac`, `sleep`, `dbg_trace`, `unhygienic`,
  `grind`, and `+native`/`+kernel` (`Parser.Tactic.configItem`).
- Allowed Pass-1 tactics (`allowedTheoryTacticKinds` in `TrustedBoundary.lean`):
<!-- pass1-tactic-allowlist:begin -->
  `apply`, `cases`, `change`, `constructor`, `decide`, `dsimp`, `exact`,
  `first`, `induction`, `injection`, `intro`, `left`, `refine`, `revert`,
  `right`, `rw`, `simp`, `subst`, `have`, `let`, `nomatch`, `repeat`, `rfl`,
  `unfold`, `funext`, `<;>`
<!-- pass1-tactic-allowlist:end -->

## Step 5: Escape Tabu verification cliffs

If proof complexity crosses **`> 15:1` Lean-to-Rust LOC** or you remain stuck on
the same goal across **2 focused turns** without shrinking the remaining goal:

1. **Do not thrash.** Stop adding ad-hoc `simp` rules or raw case splits.
2. **Isolate the bottleneck:** Extract the smallest failing sub-lemma or check
   whether a Rust helper extraction / loop split / invariant rewrite makes the
   MIR WP cleanly separable (propose Rust helper refactors to the caller; do
   not silently alter `Spec.*` or out-of-scope Rust files).
3. **Rollback failed exploratory proof edits** (`git checkout -- ...` on your
   own scratch proof branch) before trying a new representation shift from
   Step 3.
4. Once `Expected.claim` elaborates cleanly without `--allow-sorry-in-proof`,
   return to **`cargo-anneal`** to capture and report the final untainted
   Receipt v3.
