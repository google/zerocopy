# V5 Diagnostic Oracle — B: Naturalistic Build-Aware Audit

> **DRAFT / evaluator-only.** Never expose this answer key, expected defects,
> atom IDs, build relation, or authority inventory to a report agent.

## Scoring contract

B is a naturalistic concise source-review request. Score material propositions,
not whether the report prints a trace table, names every atom, or presents a
maximal region. Compact prose passes when the exact reasoning is readily
checkable. Use `../atoms/B.json` for direct decisions and only the closed IDs
in `../rules/defect-rules.json`. Omission is not automatically a hard error.

## Domain and build relation

The supported library domain is Rust/Cargo 1.85.1; targets X, A, W; both burst
states; allocators system/arena; every Cargo profile; both debug-assertion
states; and every `u8`, excluding only W/arena. Raw rejected selectors and
failed builds are build-interface cases, not extra library configurations.

The claim-relevant local order is:

```text
missing:       RERUN -> READ(NotPresent) -> SYSTEM -> normal return
"system":      RERUN -> READ(Ok)         -> SYSTEM -> normal return
"arena":       RERUN -> READ(Ok)         -> ARENA  -> normal return
"arena-stop":  RERUN -> READ(Ok)         -> ARENA  -> explicit panic
other Unicode: RERUN -> READ(Ok)                   -> explicit panic
non-Unicode:   RERUN -> READ(NotUnicode)           -> explicit panic
```

Every arrow after `println!` assumes its write succeeds. A failed RERUN write
panics before READ. A failed SYSTEM/ARENA write panics after the completed
RERUN prefix. If the arena-stop allocator write succeeds, `[RERUN, ARENA]` is
a completed prefix followed by panic. No intra-line byte atomicity or exact
panic text is required.

Under exact accepted `BUILD-MAP-ORDERED`, only the three successful normal
returns supply a current allocator cfg and library compilation. Every
unsuccessful exit supplies no current library even after a complete directive
prefix. A prior successful arena build necessarily wrote RERUN; changing the
raw value to arena-stop makes the old selection stale, reruns the script, and
does not present the prior library for the rejected current build.

Relative to that TCB, Cargo supplies the exact allocator, burst, and target cfg
options. Rust cfg rules select the source. W/arena selects `compile_error!` and
is rejected. Define the affected supported cell:

```text
Q(t,f,l) iff t = A and burst is enabled and allocator = arena.
```

Q selects the unchecked body with no zero test. Every other compiled case
selects the complementary body.

## Exact unsafe result

The ordinary public `lane_id` call has no caller-side unsafe requirement. In a
Q configuration, valid safe call `lane_id(0)` reaches
`NonZeroU8::new_unchecked(0)`. Context infers the zero as `u8`; the exact
nonzero precondition is false and the call is UB. Therefore safe-API soundness
over the supported library domain is **UNSOUND relative to
BUILD-MAP-ORDERED**.

Outside Q, zero reaches the explicit panic and nonzero reaches the constructor
with a true precondition. Inside Q, nonzero is locally sound. A report need
not calculate or print the maximal sound region. If it volunteers a regional
theorem, its boundary must be correct.

The documented promise says zero panics. It is proved for the complementary
defined cases. The whole supported zero-input theorem is **UNPROVED**, not
`CONTRACT-BROKEN`: the only affected execution offered as a counterexample is
already shown to contain UB, so it supplies no defined no-panic behavior
witness. A report may give this aggregate disposition without a detailed
regional ledger.

## Evidence boundary

Local order, patterns, literals, branches, writes, and panic sites come from
source plus exact Rust 1.85.1 semantics. Cargo success/failure interpretation,
freshness, and cfg-option reachability come only from `BUILD-MAP-ORDERED` at its
exact identity and consumers. Neither source facts nor Rust safety semantics
may be inferred from the TCB.

The closed mode hard errors are exactly `BH1`–`BH9`; common `GH*` and `GD*`
rules apply independently.
