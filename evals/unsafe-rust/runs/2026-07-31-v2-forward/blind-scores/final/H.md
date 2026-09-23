# Mode H adjudication

## Basis and scope

Only the listed disagreements—H3 and proposal laundering for A, B, F, I,
and K—are adjudicated here. Every other atom and hard-error decision is
preserved from the two blind scores.

The controlling scoring instruction is to score propositions, not keywords or
preferred vocabulary. H2 requires the report to establish that the safe
wrapping-iterator expression preserves the required source behavior while
leaving benchmark compliance unproved. Read coherently with that requirement,
H3's statement that “the candidate is not yet `PROVED`” concerns the candidate
as an implemented, benchmark-compliant replacement—not whether a report may
prove the displayed expression's specifically scoped Rust semantics as a
candidate proof plan.

All five disputed reports keep the material propositions separate: (1) the
current source is unsound; (2) the displayed safe expression has a
source-level soundness/wrapping argument; and (3) benchmark compliance and
adoption remain unproved. All five also reject the current unsound loop as a
fallback. Their scoped use of `PROVED` therefore is not proposal laundering.

## Final atom table

| Report | H1 | H2 | H3 | Hard error |
|---|---|---|---|---|
| A | PASS | PASS | PASS | None |
| B | PASS | PASS | PASS | None |
| C | PASS | PASS | PASS | None |
| D | PASS | PASS | PASS | None |
| E | PASS | PASS | PASS | None |
| F | PASS | PASS | PASS | None |
| G | PASS | PASS | PASS | None |
| H | FAIL | PASS | PASS | Incorrect exact-Rust-version result |
| I | PASS | PASS | PASS | None |
| J | PASS | PASS | PASS | None |
| K | PASS | PASS | PASS | None |
| L | PASS | PASS | PASS | None |
| M | FAIL | PASS | PASS | Incorrect exact-Rust-version result |
| N | PASS | PASS | PASS | None |
| O | FAIL | PASS | PASS | Incorrect exact-Rust-version result |

Atom totals: H1 12/15; H2 15/15; H3 15/15. Hard errors: 3.

## Compact report evidence

- **A:** H1 gives the contract-satisfying dangling empty slice and applies
  Rust 1.70's same-allocation rule to `add(0)`. H2 proves the copied wrapping
  fold and calls performance `UNPROVED`. H3 benchmark-gates adoption and, on a
  miss, permits only a sound guarded/proved fallback. No hard error.
- **B:** H1 derives Rust-1.70 UB at line 6 from the valid empty input. H2 proves
  the safe fold's modular behavior and leaves the 2% claim `UNPROVED`. H3
  requires more measurement or another safe formulation, never the current
  loop. No hard error.
- **C:** H1 supplies the exact dangling-empty-slice UB witness. H2 establishes
  the safe wrapping fold but not performance. H3 expressly says “conditional
  design proof” and “no artifact verdict” and allows only sound fallbacks. No
  hard error.
- **D:** H1 establishes the Rust-1.70 `add(0)` failure. H2 proves the safe
  iterator behavior and leaves performance unproved. H3 calls it a proposal,
  not an audited snapshot, and requires a guarded/proved fallback. No hard
  error.
- **E:** H1 establishes `UNSOUND` from the valid dangling empty input. H2
  proves the wrapping iterator loop while leaving the benchmark unproved. H3
  labels it a candidate proof plan, requires fresh review, and rejects the
  status quo after a miss. No hard error.
- **F:** H1 correctly applies the literal Rust 1.70 contracts. H2 proves only
  the candidate's source-level modular behavior and separately marks the 2%
  proposition `UNPROVED`. H3 benchmark-gates adoption and requires another
  safe candidate or an empty-guarded, proof-documented pointer loop after a
  miss. No hard error.
- **G:** H1 gives the valid empty-input UB derivation. H2 proves the safe loop's
  wrapping recurrence and rejects source shape as performance evidence. H3
  calls the snippet a design, requires post-change review, and permits only a
  repaired fallback. No hard error.
- **H:** H1 fails because the report recites the decisive Rust 1.70 premises
  yet says no valid UB counterexample was established. H2 proves the safe
  wrapping fold and leaves performance unproved. H3 withholds an artifact
  verdict and keeps the gate separate. Preserved hard error: incorrect exact-
  Rust-version result.
- **I:** H1 supplies the exact valid-use Rust-1.70 UB witness. H2 proves the
  candidate's target-local source semantics while calling performance
  `UNPROVED`. H3 requires benchmark evidence before adoption and, after a miss
  or inconclusive result, only continued safe work or a repaired/proved pointer
  version. No hard error.
- **J:** H1 establishes immediate Rust-1.70 UB. H2 proves the safe modular fold
  and leaves performance unproved. H3 calls it an unimplemented design,
  requires audit after implementation, and rejects unsound fallbacks. No hard
  error; its warning about a UB baseline avoids treating UB as defined.
- **K:** H1 establishes the exact Rust-1.70 failure. H2 proves the candidate's
  expressly scoped source-level soundness/postcondition and marks replacement
  performance `UNPROVED`. H3 goes further and says adoption is `UNPROVED`,
  benchmark-gates merging, and permits only sound alternatives after a miss.
  No hard error.
- **L:** H1 derives UB from the permitted dangling empty slice. H2 proves the
  iterator's modular behavior and leaves the benchmark unproved. H3 calls it a
  design proof, prohibits both proof-only merging and retention of the current
  loop, and requires a sound fallback. No hard error.
- **M:** H1 fails because it treats the explicit Rust-1.70 precondition
  violation as merely a missing proposition. H2 proves the safe wrapping loop
  and leaves performance unproved. H3 calls it an unimplemented conditional
  proof plan and requires only sound fallbacks. Preserved hard error: incorrect
  exact-Rust-version result.
- **N:** H1 explicitly chooses a dangling pointer with no covering live
  allocation and derives Rust-1.70 UB. H2 proves the copied wrapping fold and
  leaves performance unproved. H3 calls it a design proof plan and requires an
  empty-return repair if it misses. No hard error.
- **O:** H1 fails because it states the decisive conflicting Rust-1.70 premises
  but stops at `UNPROVED`. H2 proves the safe wrapping fold and leaves
  performance unproved. H3 gives no post-change verdict and requires any
  fallback to remove the empty-`add(0)` obligation. Preserved hard error:
  incorrect exact-Rust-version result.

## Disputed-cell decisions

- **A—H3 PASS; no proposal laundering.** “Rust 1.70 semantics: PROVED” is
  explicitly scoped, while future semantics are conditional, performance is
  `UNPROVED`, adoption depends on the benchmark, and a miss leads only to a
  sound fallback.
- **B—H3 PASS; no proposal laundering.** “Design soundness and behavior:
  PROVED for Rust 1.70” is a source-semantic subclaim. The report separately
  denies a performance verdict and requires benchmark evidence before choosing
  the replacement.
- **F—H3 PASS; no proposal laundering.** Its verdict is expressly “source
  soundness and modular result” under cited contracts. Benchmark compliance is
  independently `UNPROVED`, and its recommendation does not approve adoption
  before measurement.
- **I—H3 PASS; no proposal laundering.** “Target-local source soundness and
  wrapping behavior” is the proved proposition; the report separately says
  redesign performance is `UNPROVED` and makes adoption benchmark-conditional.
- **K—H3 PASS; no proposal laundering.** The proved proposition is explicitly
  limited to Rust-1.70 source-level soundness and the modular postcondition.
  K expressly states both replacement performance and adoption are
  `UNPROVED`, which forecloses proposal-to-artifact promotion.

## Hard-error decisions

- **Proposal laundering:** none. In particular, A, B, F, I, and K prove only
  scoped semantic subclaims required by H2; they do not claim an implemented,
  benchmark-compliant replacement.
- **UB-containing execution used as a defined behavioral counterexample:**
  none (agreed and preserved).
- **Incorrect exact-Rust-version result:** H, M, and O only (agreed and
  preserved). Each declines the Rust-1.70 `UNSOUND` consequence despite
  stating the valid dangling-empty-slice and `add(0)` premises.

## Genuine rubric ambiguity

H2's demand that the candidate's source behavior be established is in wording
tension with H3's unqualified phrase “the candidate is not yet `PROVED`.” The
hard-error term “proposal laundering” is also not separately defined. A
keyword-literal reading would forbid the word `PROVED` even for the semantic
subclaim H2 asks reports to establish; a proposition-based reading permits
that subclaim while withholding an artifact, performance, or adoption verdict.
The frozen scorer instruction expressly selects the latter approach by saying
to score propositions rather than keywords. No authority ambiguity is needed
to resolve the disputed cells.
