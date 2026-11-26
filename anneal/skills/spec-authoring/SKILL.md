---
name: spec-authoring
description: >-
  Use when translating Rust or C reference intent into formal Anneal Lean
  specifications, auditing specs for echo or vacuity traps, checking client
  sufficiency, or separating spec changes from proofs. Not for CLI flags or
  receipt parsing (use cargo-anneal) or Lean proof scaling (use proof-scaling).
---

# Author and audit Anneal specifications

Good proofs of weak, vacuous, or echoed specs create false confidence. Author
and freeze `Spec.lean` / `Spec.*` (`AuthoredRole::Specification`, defining
`Spec.specs` of type `Trusted.MirSemantics.Specs` with `Specs.safety` and
`Specs.property`) before investing in `Proof.lean` / `Proof.*`.
`specification` modules define *what* holds; they must not import `Anneal.*`
proof libraries (rejected by audit).

## Step 1: Body-last spec archaeology

Do **not** read the Rust implementation body to invent the spec. Gather **`>= 2`
non-body channels first** and synthesize an initial contract from them plus the
Rust signature:

1. Docstrings, `/// # Safety` comments, type invariants, and module docs.
2. Unit tests, doc tests, Miri tests, and real callers / downstream clients.
3. Upstream RFCs, reference C/hardware specs, or ABI documentation.

Only after writing the initial `Specs.safety` (caller preconditions) and
`Spec.specs` / `Specs.property` (postconditions) from those channels, inspect
the Rust body to check edge behavior (integer width, error variants,
truncation).

**Discrepancy rule:** If the Rust body contradicts `>= 2` non-body channels,
stop and raise an **Intent Decision** with the user (bug in Rust vs stale docs).
Never silently relax a spec to fit suspicious code.

## Step 2: Trap-free total-logic defaults

Write specs in pure Lean term logic importing `prelude` plus only pinned
`Init.*` modules (`trusted/lean/foundation-lock.json` and
`trusted/audit/library-lock.json`, e.g., `Init.Data.BitVec.Basic`). Monolithic
`import Init` (`~473 MiB` RSS vs `~152 MiB` targeted) is rejected fail-closed in
pinned `cargo anneal verify` unless `--allow-unpinned-lean` is passed.

- **Total correctness default:** Require termination (`¬ Diverges` /
  `Behavior`, ensuring `wpProg` / `execProg` fuel covers execution to return or
  unwound outcome rather than hitting a `fuel = 0` `False` cutoff) unless the
  item is explicitly documented to loop or abort on stated inputs.
- **Exact machine arithmetic:** Model fixed-width and signed operations via
  `BitVec w` and `Int.tdiv` (or explicit integer bounds), not partial `Nat`.
- **Zero unguarded partial traps:** Never rely on saturating `Nat.sub` (`a - b`
  clamping to `0`), totalized `Nat` `/` or `%` (`x / 0 = 0`), or unguarded
  `BitVec.toNat` / `Int.toNat` casts. Either prove domain preconditions exclude
  underflow/division-by-zero in `Specs.safety`, or represent truncation
  explicitly.
- **Explicit non-vacuous `Specs.safety`:** State exact input bounds and domain
  invariants callers must establish (note: current scalar Profile v1 rejects
  pointers/references and enforces empty caller memory). Writing `False` in
  `Specs.safety` lets proofs pass trivially while admitting zero callers.

## Step 3: Anti-echo and client-sufficiency gate

Reject **tautological echo specs** that merely copy the Rust control flow or
arithmetic AST branch-for-branch into Lean. State mathematical or behavioral
properties that an independent reader can verify: bounds, conservation laws,
bit-exact equivalence to a simpler scalar/reference model, order preservation,
or round-trip invertibility.

Check **client sufficiency** before freezing the spec:
- Identify real caller expectations (tests, callers, or downstream invariants).
- Write a temporary scratch `theorem` (note: `spec-preflight` permits `theorem`
  and excludes `example` in `Spec` modules) proving the caller's needed
  post-state property using **only** `Specs.safety` + `Specs.property`
  (never peeking into `Proof.*` or `Captured.lean`), then remove it before
  commit.
- Record a clause coverage tally in your review note or commit context:
  `clauses: N, client-exercised: M`. Justify any unexercised clause (`M < N`)
  or prune dead spec obligations.

## Step 4: `[A4]` pre-proof sanity and dual-polar mutation checks

Run these lightweight checks *before* writing `Proof.*`, and label results
explicitly as assumptions-only `[A4]` sanity (never as a replacement for
proofs):

1. **Vacuity & consistency (`cargo anneal verify`):** Check a temporary scratch
   `theorem` witnessing concrete valid arguments satisfying `Specs.safety`, and
   a valid `(input, output)` pair satisfying `Specs.property` (`Spec` admits
   `theorem`, not `example`). Confirm `Specs.safety` cannot derive `False`,
   then delete the temporary `theorem`.
2. **Dual-polar mutation check (temporary, revert before committing):**
   - **Negative polarity (wrong body):** Temporarily perturb a return value or
     comparison in Rust (e.g., `+ 1` or `<` -> `<=`) and verify either
     `cargo test` fails or `Expected.lean` rejects the unguarded spec.
   - **Positive polarity (forbidden input):** Verify a caller violating one
     conjunct of `Specs.safety` cannot satisfy the precondition witness.

## Step 5: `Spec` vs `Proof` separation and handoff

Keep specification edits cleanly isolated from proof edits:
- Put `Spec.lean` / `Spec.*` and `request.json` scope/precondition updates in
  their own reviewable commit ahead of `Proof.lean` / `Proof.*` changes.
- Classify every spec diff explicitly using a `Spec-Change:` line in the commit
  or PR note: `initial` | `tightening` | `weakening` | `refactor`.
- Any `weakening` requires explicit user authorization and re-running Steps 3-4.

Once the spec passes Steps 1-4, hand off to **`proof-scaling`** to prove
`Expected.claim`, or to **`cargo-anneal`** for single-command verification.
