<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Proof and Code Modularity, Kernel Cost, and Zero-TCB Auto-Scaffolding

This guide collects engineering guidance for Lean 4 proof modularity, kernel
proof-term footprint, deterministic `AutoScaffold.lean` generation, and
non-proof Lean/Rust factoring across Anneal. It is advisory: the only
merge-blocking checks are the hard gates in §4, which
[`ci/proof_health_scan.py`](../ci/proof_health_scan.py) implements. Companion
user-facing workflows live in
[`cargo-anneal`](../trusted/cargo-anneal/skills/cargo-anneal/SKILL.md),
[`proof-scaling`](../skills/proof-scaling/SKILL.md), and
[`spec-authoring`](../skills/spec-authoring/SKILL.md).

## 1. Surface-Partitioned Optimization Objectives

Different artifact classes fail in opposite ways under naive size pressure:

- **Specifications (`Spec.lean` / `AuthoredRole::Specification`):** Exempt from
  line-count, `.olean`, or token minimization. Optimize solely for semantic
  clarity, non-vacuity, anti-echo, and client sufficiency (`spec-authoring`).
- **Target Rust Proofs (`TargetRole::Proof`, e.g. `zerocopy/proofs/`):** Isolate
  mechanical MIR wiring inside deterministic `AutoScaffold.lean` (Layers S1+S2)
  and optimize hand-authored `Proof.lean` (Layer S3) jointly for modular domain
  structure, small `.olean` / `Expr` DAG+tree size, and fast kernel replay.
- **Pass-1 Proof Libraries (`anneal/theory/` and `anneal/correspondence/`):**
  Target `<= 35` non-blank lines per new theorem (`<= 60` soft review ceiling).
  Split `> 60`-line case-dispatch proofs over `Rvalue`, `TerminatorKind`, or
  `BlockCfg` constructors into shared per-case helpers (`>= 2` call sites) so
  updating one MIR construct re-elaborates only its helper lemma. Never extract
  trivial single-use pass-through wrappers solely to hit a line count.
- **Non-Proof Computable Lean (`def`, `structure`) and `trusted/` Rust:**
  Apply duplication and branch-complexity pressure (`robust-code`), never raw
  character/line minimization or `.olean` constant-count minimization. Preserve
  100% of `/// # Safety` rationales, upstream `rust-lang/rust` pinned citations,
  exhaustive enum matches (zero new `_ =>` wildcards on security-relevant AST
  or role enums), and distinct `Error` phase/status diagnostics
  (`comment-guidelines`).

## 2. Three-Layer Zero-TCB `AutoScaffold` Architecture

[`ci/anneal_scaffold.py`](../ci/anneal_scaffold.py) reads `capture.json` and
renders `AutoScaffold.lean` as an untrusted `"role": "proof"`
(`TargetRole::Proof`) module. `cargo-anneal verify` exports and replays
`AutoScaffold.lean` in a fresh Lean kernel environment (`trustLevel := 0`)
against unmodified `Expected.claim` and `Spec.specs`, adding zero lines to
`trusted/lean/`, `TrustedBoundary.lean`, `SpecPreflight.lean`, or
`Expected.lean`:

1. **Layer S1 (Identity & ABI Wiring):** Collision-free `id_<slug>`,
   `body_<slug>`, `get_<slug>`, `adm_<slug>`, typed `ValidEntryArgs`
   eliminators, unified `ok_<slug>` (`BodyVerified ∧ ScafReturnsTotal`), and
   `all_bodies_safe` dispatch. Survives declaration reordering (`P2`) in `O(1)`
   kernel `rfl` cost without runtime `stringBeq` folds.
2. **Layer S2 (Symbolic Straight-Line Stepping):** Lowers local storage
   markers, scalar copy/move chains (`P1`), and straight-line bitwise or
   comparison temporaries (`P3`) using explicit `let s_k := mkState 0 k [...]`
   state bindings and parameterized `Anneal.MirWp` step lemmas with zero `simp`
   calls.
3. **Layer S3 (`Proof.lean`):** Hand-authored mathematical domain lemmas and
   `Proof.verify : Expected.claim`, free of positional `DefId` literals,
   `Captured.body_N` cross-references, and temporary slot indices.

In `zerocopy/proofs/`, `AutoScaffold.lean` is checked in alongside `Proof.lean`
and verified byte-for-byte against `capture/capture.json` on every
[`ci/verify_zerocopy.py`](../ci/verify_zerocopy.py) run. Regenerate after a
Rust MIR change via:

```sh
python3 -I -B anneal/ci/anneal_scaffold.py \
  --request zerocopy/proofs/<unit>/request.json
```

CI's `installed-smoke` job also runs the live test in
[`ci/test_anneal_scaffold.py`](../ci/test_anneal_scaffold.py), which
kernel-checks generated scaffolds, including the `u64` templates that no
checked-in unit uses yet.

## 3. Proof-Authoring Checklist

Optimize jointly for **modular semantic structure, small compiled `.olean` /
`Expr` DAG+tree size, and fast kernel replay**, never for raw source line or
character count alone:

1. **Reuse `Anneal.*` first; prune only unused `Init.*`:** Before proving
   bitwise, modular, or linear-arithmetic lemmas by hand, check bundled
   `Anneal.BitVecArith`, `Anneal.BitVec`, `Anneal.NatBitwise`,
   `Anneal.LinearArith`, `Anneal.BitTrieLrat`, and `Anneal.InitLemmas` (reusing
   `Anneal.BitVecArith` also avoids unnecessary `Classical.choice` axioms).
   Prune unused `Init.*` imports for RSS, never bundled `Anneal.*` helpers.
2. **Unify safety + totality and isolate MIR layout:** Prove
   `(BodyVerified ... ∧ ReturnsTotal ...)` (or
   `WellFormed ... ∧ ReturnsTotal ...`) in a single pass per body instead of
   stepping the same MIR twice. Confine `DefId`, `BodyStaticAdmitted`,
   `ValidEntryArgs`, and straight-line local-slot traces to generated
   `AutoScaffold.lean` (`TargetRole::Proof`) or per-body leaf lemmas keyed by
   `b.identity`; never hardcode positional `DefId` indices or cross-reference
   sibling `Captured.body_N` slots.
3. **Bind intermediate states (`let s_k`) to prevent `Expr` tree bombs:** In
   `Executes.next` / `wpState` chains, bind each intermediate state via
   `let s1 := mkState ...` and pass `.next (next := s1) ...`. Never nest
   `erw [show ...]` or un-named `mkState` terms inside deep `.next` chains,
   which can explode unfolded `Expr` trees past `10^8` nodes while looking
   small in source LOC.
4. **Never feed AST/semantics evaluators into `simp`:** Passing `MirTy.beq`,
   `IntWidth.beq`, `evalStep`, `evalRvalue`, or `writePlace` to a `simp`
   lemma list synthesizes hundreds of hidden `_private.*.match_*` and
   `.splitter` declarations (`5x-10x` `.olean` bloat). Use parameterized
   `step_*` lemmas (`Anneal.MirWp`) or targeted `unfold ...; rw [...]`.
5. **Factor multi-use lemmas (`<= 20L` target; split `> 60L` Pass-1 proofs):**
   Keep target `Proof.lean` lemmas `<= 20` non-blank lines where natural and
   refactor Pass-1 `theory/` or `correspondence/` theorems exceeding `60` lines
   into shared per-case lemmas when `>= 2` branches share structure. Do not
   extract trivial single-use pass-through wrappers solely to hit a line count.
6. **Readable, honest proofs:** Keep `<= 100` columns and descriptive names;
   avoid `simp [*]`, `simp_all`, `<;>` soup, `local macro` packs, and large
   `by rfl` / `by decide` WHNF reductions that spike kernel replay time; and
   never alter `Spec.*` to shorten a proof.

## 4. Hard Anti-Golf Gates vs. Advisory Burden Telemetry

[`ci/proof_health_scan.py`](../ci/proof_health_scan.py) (enforced in CI
`Static checks` and [`ci/verify_zerocopy.py`](../ci/verify_zerocopy.py))
separates merge-blocking Lean proof-hygiene invariants from continuous
engineering advisories (source LOC or `proof_loc / rust_loc` ratios are never
enforced as hard CI gates):

- **Hard Hygiene Gates (`--check-hygiene`):**
  1. *Spec-immutability gate (proof units under `zerocopy/proofs/` only):*
     the check judges the change that merging `HEAD` into `base_ref` would
     make (the tree diff from `base_ref` to the result of
     `git merge-tree --write-tree <base_ref> HEAD`, with rename detection),
     not individual commits. It fails if that diff modifies, deletes, or
     renames an existing unit's `request.json` or any source that
     `request.json` at `base_ref` declares with `"role": "specification"`,
     unless a commit in `base_ref..HEAD` carries a
     `Spec-Change: <unit> <kind>` Git trailer (`<kind>` is `initial`,
     `tightening`, `weakening`, or `refactor`). A merge conflict on a
     protected path counts as changing it. An in-place edit of a
     regular-file `request.json` that only adds, removes, or changes
     proof-role sources is allowed. Malformed `Spec-Change` trailers fail;
     prose mentioning `Spec-Change:` outside the trailer block is ignored.
     Units absent from `base_ref` are not protected. `base_ref` defaults to
     `origin/main`, or `main` if that does not exist.
  2. *Syntactic anti-golf on `.lean` proofs:* `<= 100` columns in `.lean` code
     (alongside the repository's standing `80`-column rule for Markdown and
     comments and `rustfmt` check on `.rs`); `<= 2` tactic semicolons per line;
     zero `simp [*]`, `simp_all`, `local macro`, or `macro_rules`; and zero AST
     or operational evaluators (`MirTy.beq`, `IntWidth.beq`, `Place.beq`,
     `evalStep`, `evalRvalue`, `evalTerminator`, `writePlace`) in the lemma
     list of any `simp`, `dsimp`, `simpa`, or `simp_arith` call (with or
     without `only`, `+opt`/`-opt` flags, or `(config := ...)`); the `*`
     wildcard is rejected anywhere in such a list, across lines. Files under
     `anneal/theory/` and `anneal/correspondence/` are ratcheted against
     `git merge-base <base_ref> HEAD`: only new violations fail, comparing
     renamed files against their base content.
- **Dead-Helper Mop-Up (`--unused-private`):** After landing a proof-refactoring
  or scaffolding batch, run
  `python3 -I -B anneal/ci/proof_health_scan.py --unused-private` (defaults to
  `zerocopy/proofs/*/Proof.lean`; pass `--paths anneal/theory` or
  `--paths anneal/correspondence` for Pass-1 libraries) and remove orphaned
  `private` declarations whose external reference count dropped to `0`.
- **Advisory Telemetry (`--telemetry`, `anneal-perf-record/v1`):** Tracks
  `proof_burden.*` (`hand_proof_loc`, `scaffold_loc`, `spec_loc`, `max_thm_loc`,
  `proof_olean_bytes`, `module_union_dag`, `sum_val_tree`, `tree_to_dag_ratio`,
  `kernel_replay_ms`, and `gt_60_thm_count`). The `--telemetry` JSON report
  also lists non-blocking review advisories when target `Proof.lean` theorems
  exceed `20` non-blank lines, Pass-1 theorems exceed `60` non-blank lines, or
  `tree_to_dag_ratio > 50`. [`ci/perf_tracking.py`](../ci/perf_tracking.py)
  records only the `proof_burden.*` metrics, and profiles compiled modules only
  when the `proof_burden` category is selected.
