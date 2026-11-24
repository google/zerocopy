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
   runs, pass `--lean-memory-mb <MB>` (or wrap CLI `lake` / `lean` builds in
   an OS cgroup memory cap), and do not launch parallel unbounded `lean` builds.
3. Diagnose **Day-2 Rust bugs** first (`cargo-anneal` Step 0): if `Expected.lean`
   reveals a missing guard or bad branch in Rust, fix Rust or escalate the spec
   mismatch before tuning tactics.

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
- Linear arithmetic Farkas certificates (replaces `omega` in Pass 1):
  `Anneal.LinearArith`
- Bitvector/SAT LRAT certificates (replaces `bv_decide` in Pass 1):
  `Anneal.BitTrieLrat`, `Anneal.BitVec`, `Anneal.BitVecArith`
- Classical law-of-excluded-middle & core `Init` helpers (replaces `by_cases`
  in Pass 1): `Anneal.ClassicalEm`, `Anneal.InitLemmas`, `Anneal.NatBitwise`
- MIR WP, loop invariants, byte/chunk layouts, forcing, firewalls, and trees:
  `Anneal.MirWp`, `Anneal.LoopInv`, `Anneal.LeBytes`, `Anneal.ListChunks`,
  `Anneal.PTree`, `Anneal.SpineForce`, `Anneal.Firewall`
<!-- pass1-bundled-modules:end -->

Note: repo-local `anneal/theory/Anneal/PureLift.lean` (and `MirTotal`, `Core`)
exist in-tree for WP/PureLift development, while `theory/bundle-manifest.json`
governs which `Anneal.*` modules `cargo anneal verify` bundles into standalone
target proofs.

**6 algebraic representation shifts (when elaboration or `whnf` explodes):**
1. **Import `prelude` + targeted `Init.*` (`~152 MiB` vs `~473 MiB`):** Pinned
   `cargo anneal verify` and `anneal/theory/` reject monolithic `import Init`
   fail-closed; import `prelude` plus only the specific pinned `Init.Data.*`
   modules (`foundation-lock.json` in `anneal/theory/`, plus
   `library-lock.json` in pinned `cargo anneal verify`).
2. **Defunctionalize closures and higher-order combinators:** Replace captured
   `fun` closures inside proof-carrying states with small inductive tags + an
   explicit `eval` function so kernel unification never reduces huge lambda terms.
3. **Zero-`Prop`-arg `@[irreducible]` barriers + flat-tuple `casesOn`:** Wrap
   large sub-expressions behind `@[irreducible]` definitions taking data args
   only (no `Prop` fields hiding proofs inside data terms), and destructure flat
   product tuples with `casesOn` rather than chained `.1`/`.2` projections.
4. **Logarithmic lookup & chunked lists:** Replace linear `List` indexing /
   deeply nested updates with `Anneal.PTree` (path trees) or `Anneal.ListChunks`.
5. **Control reduction eagerly:** Use `Anneal.SpineForce` to force spine shapes
   before `rw`/`simp` instead of letting `whnf` unfold deep bitvectors/states.
6. **Lift pure regions first:** Factor pure computation with `Anneal.MirWp`,
   `Anneal.LoopInv`, and `Anneal.BitVec` (and `PureLift` in `theory/`) before
   reasoned arithmetic/bitvector certs.

## Step 3b: Proof modularity and kernel footprint

For advisory modularity and kernel-footprint guidance, see §3 of
[`docs/proof-and-code-modularity.md`](../../docs/proof-and-code-modularity.md).

## Step 4: Pass-1 `TrustedBoundary` rules (for `anneal/theory/` work)

Target `proof` modules (`TargetRole::Proof`) import bundled `Anneal.*` modules
to prove `Expected.claim`. When authoring Pass-1 libraries under
`anneal/theory/` or `anneal/correspondence/` (`SourceRole.theory`),
`TrustedBoundary.lean` enforces:
- Imports: `prelude` + foundation-pinned `Init.*` (`trusted/lean/foundation-lock.json`)
  + `Trusted.*` + `theory/` modules in `anneal/theory/` (`anneal/correspondence/`
  also admits sysroot foundation `Init.*`/`Std.*`/`Lean.*`, vendored `lean-miri`,
  and sibling `correspondence/` modules); axioms strictly in
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
   own scratch proof branch) before trying a new representation shift from Step 3.
4. Once `Expected.claim` elaborates cleanly without `--allow-sorry-in-proof`,
   return to **`cargo-anneal`** to capture and report the final untainted Receipt v3.
