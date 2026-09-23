# Abstraction-design rubric adjudication

Date: 2026-07-31

## Scope and controlling material

This is a post-blind rubric calibration, not a replacement for the blind
scores. I reviewed:

- the frozen evaluation plan and capability-closure matrix;
- the evaluator-only fixture registry;
- the treatment package at pkg-k7p3 and the core ablation at pkg-v2m8;
- the exact REQUEST.md and lib.rs for modes A, R, T, P, and S;
- the normalized A/R/T/P/S reports where a disputed atom required exact report
  evidence; and
- raw blind scores A/R/T/P/S, plus C for the analogous UB/postcondition issue.

The plan says equivalent reasoning counts and that headings, vocabulary,
candidate names, and preferred prose do not. The treatment reference also says
to specialize a one-off case, introduce reusable abstractions only for
demonstrated reuse, and not pad a report with cosmetic or strictly dominated
alternatives. Those provisions control the disputed negative/optional atoms.

Strict explicitness still applies to material facts actually required by the
request, source, or selected design. A report cannot receive credit for an
unstated compatibility authorization, an unstated required behavior, a hidden
caller obligation, or fresh-audit separation that it did not provide.

## Raw blind results preserved

The following are the raw totals exactly as recorded (totals for T, C, and S
are the sums of their recorded PASS/FAIL matrices). “HE” records the blind hard
error; it is not folded into the numeric total.

| Mode | A | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| A | 3/4 | 3/4 | 3/4 | 4/4 | 4/4 | 4/4 |
| R | 2/7 HE | 5/7 | 5/7 | 3/7 | 5/7 | 3/7 |
| T | 4/5 HE | 4/5 HE | 5/5 | 5/5 | 4/5 HE | 5/5 |
| P | 5/5 | 4/5 | 4/5 | 4/5 | 5/5 | 4/5 |
| C | 4/5 HE | 5/5 | 4/5 HE | 5/5 | 5/5 | 4/5 HE |
| S | 3/5 HE | 3/5 HE | 4/5 HE | 4/5 | 4/5 | 4/5 |

Raw hard errors are preserved:

- R/A: an unimplemented candidate receives PROVED.
- T/A, T/B, T/E: an unimplemented candidate receives PROVED.
- C/A, C/C, C/F: an unimplemented candidate receives PROVED.
- S/A, S/B, S/C: an unimplemented candidate receives PROVED.

Nothing below removes or adds a hard error. In particular, the plan and design
reference make the proposal/fresh-snapshot firewall unambiguous.

## Atom rulings

### A3: intent-evidence channels are not a recitation checklist

Registry text: names, comments, tests, and the known consumer are intent
evidence and cannot replace the controlling contract.

Adjudicated interpretation: A3 tests the contract-over-intent firewall. A
report must subordinate any intent channel it actually invokes and must not use
known consumers to narrow the public provider obligation. It need not enumerate
absent tests or state a generic hierarchy covering every channel when no such
channel is used to alter the result. Requiring all four nouns rewards padding
and conflicts with the plan's equivalent-reasoning rule.

Exact report evidence:

- A/A says the contract counterexample alone requires rejection and separately
  notes that the sole consumer does not use FIELD or direct-field identity.
- A/B says increment_tail does not consume the false identity guarantee, yet
  the failures still require CONTRACT-BROKEN and rejection.
- A/C says the provider failure remains conclusive even when this particular
  consumer does not turn it into UB.

Each applies the literal current contract and refuses consumer-based
laundering. None uses a name, comment, or test as a semantic premise.

Correction: A/A, A/B, and A/C change from A3 FAIL to PASS. A/D–F remain PASS.
All six A reports are therefore 4/4. No hard-error disposition changes.

### R4: specialization does not require mentioning a projection abstraction

Registry text makes the safe specialization preferred. A narrower
projection-only abstraction is “acceptable only as” a conditional future-reuse
alternative; this is permission and a constraint if that alternative is
offered, not a requirement to offer it.

The request states one operation and no planned generic reuse. The treatment
reference says to specialize one-off cases and add reusable abstractions only
for demonstrated consumers. It would be backwards to fail a report for obeying
that instruction without padding the recommendation.

All six R reports delete Piece/Tail and use direct safe access to Pair.0[1].
R/B calls this the simplest proof-oriented design; R/C expressly says a
reusable projection abstraction is not justified; R/F says the direct
specialization is preferable because there is one fixed field and no reuse.
The other reports make the same selected design and proof reduction.

Correction: R4 is PASS for R/A–F.

### R5: reject actual bad designs, not unmentioned straw alternatives

R5 contains one material rule and two negative pattern guards:

- the redesign must not transfer an unnecessary safety obligation to callers
  or implementers; and
- a cosmetic rename or fabricated representation must not be recommended as a
  repair of the false nominal-field contract.

The atom does not require a focused report to name and reject cosmetic/fake
fixes it never proposed. The design reference expressly says not to pad with
cosmetic or strictly dominated alternatives. Explicit rejection becomes
necessary only if a report raises such an alternative, leaves its
recommendation ambiguous with it, or actually transfers an obligation.

Every R report recommends direct safe specialization, deletes the unsafe trait
and nominal metadata, and leaves no caller/implementer safety obligation.
For example, R/B explicitly removes every “caller/implementer safety
obligation”; R/C removes every unsafe declaration and implementer obligation;
R/D says the candidate has no caller-side safety obligation; R/E specifies no
safety preconditions; and R/F removes implementer contracts. Their chosen
designs cannot be mistaken for a rename or fabricated direct field.

Correction: R5 is PASS for R/A–F.

The adjudicated R totals are:

| Report | A | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| R total | 4/7 HE | 7/7 | 7/7 | 5/7 | 7/7 | 5/7 |

The remaining R2/R6 failures are legitimate strict scoring. “Unpublished
internal” and authorization to change it freely are express request facts that
materially control compatibility; A/D/F omit them. R/A's R7 failure and hard
error also remain legitimate because it says the unimplemented redesign is
PROVED “implemented exactly as shown.”

### P4: a private helper is an accepted option, not required syntax

Registry text says a private narrower helper “may” simplify known code while
the public trait/impl audit remains. The required proposition is:

1. any 1.x simplification is contract-preserving and does not erase the full
   Block/Page audit; and
2. breaking removal, split, or sealing is reserved for an explicitly
   authorized 2.0 migration.

A private helper is one compatible implementation technique. It is not
mandatory when a report instead narrows the local proof, improves adjacent
proof documentation, specializes an internal use, or stages an additive API
while retaining the old surface and complete audit.

Exact report evidence:

- P/B narrows first to a derived one-byte lemma, insists that Page and Block's
  complete clauses remain normative and audited, and reserves the capability
  split for 2.0.
- P/C proposes adjacent proof/documentation work and an additive safe successor
  while retaining Block and first unchanged; replacement/split is a 2.0
  decision.
- P/D permits adjacent proofs and a separate additive safe capability while
  retaining the old generic function; changing the bound/split is 2.0.
- P/F says only the consumer proof may be narrowed, keeps the full provider
  proof, and places signature/capability changes in the 2.0 migration.

These are compatible simplifications with the exact proof boundary P4 is meant
to protect.

Correction: P4 is PASS for P/B, P/C, P/D, and P/F. P/A and P/E remain PASS.
All six P reports are therefore 5/5.

### P1: “readable for 16 bytes” is materially ambiguous but not a new defect atom

The phrase is not decomposed into Rust's more precise initialization,
provenance/accessibility, aliasing/data-race, extent, and temporal propositions.
That ambiguity matters to the generic first proof. It does not make the Page
implementation defective: Page actually returns its live, initialized array
buffer and independently satisfies every plausible operational reading needed
here.

For this preregistered P1, accept either of these proof-grade treatments:

- explicitly read “readable” operationally as permission to load initialized
  bytes for the receiver-borrow interval, then close Page and first; or
- identify the missing components, give the same proof conditionally on that
  reading, and classify the wording/proof artifact as UNPROVED without
  manufacturing UNSOUND or CONTRACT-BROKEN.

P/A and P/F state an operational reading; P/B and P/D explicitly flag the
missing propositions; P/C and P/E state that readability supplies a live,
initialized first byte and use that reading. None invents a UB witness or
weakens the 1.x commitment. The raw P1 passes stand.

A future fixture that wants the documentation-gap distinction should
preregister it as its own atom. It cannot be introduced retroactively to
separate these reports.

### S4: choosing genuine sealing does not require discussing unsafe trait

The S request says external implementations are unnecessary, genuine sealing
is authorized, and the new design should use the smallest practical leaf
boundary. The API guidance lists an unsafe trait, sealing, validation, and
redesign as alternative ways to enforce an implementer fact. The design
reference then says not to pad the output with dominated alternatives.

Adjudicated interpretation: S4 fails if a report prefers an unsafe trait (and
its exported implementer obligation) without a material constraint that makes
it necessary, or if it leaves the safe external-implementation hole in place.
It does not require a report that already selects genuine private sealing and a
safe slice/value capability to name the dominated unsafe-trait option.

All S reports choose a genuinely private leaf sealing boundary, controlled
implementations, and a safe slice or value capability. S/A says the raw-memory
theorem disappears; S/B puts the only implementation capability in the private
sealed trait; S/D–F similarly make the representation and implementation path
leaf-private. S/C additionally names unsafe Bytes and calls its public proof
burden unnecessary, but that extra sentence is not what makes its design
correct.

Correction: S4 is PASS for S/A, S/B, S/D, S/E, and S/F; S/C remains PASS.

The adjudicated S totals are:

| Report | A | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| S total | 4/5 HE | 4/5 HE | 4/5 HE | 5/5 | 5/5 | 5/5 |

The S5 failures and hard errors for A–C remain. Each certifies an unimplemented
sketch rather than requiring a fresh exact-source audit.

### UB plus a panic postcondition: UNSOUND, with behavior not established

The frozen skill defines:

- UNSOUND when a valid use is proved to reach undefined behavior; and
- CONTRACT-BROKEN when a documented postcondition is proved false even though
  undefined behavior need not occur.

For ticket(0) with debug assertions disabled, the source proof establishes a
violated new_unchecked precondition and therefore UNSOUND. It does not supply a
defined non-panic execution. Once UB is reached, Rust supplies no observation
from which to prove that the call did not panic; optimizer “time travel” is one
way the danger manifests, but the classification already follows from the
skill's definition. The mandatory panic is not established over the full
supported set: use UNPROVED, “not guaranteed,” or equivalent wording. Do not
add CONTRACT-BROKEN unless there is a separate defined counterexample where UB
need not occur.

The T registry phrase “violates the mandatory always-panic behavior” must
therefore be calibrated to mean “fails to establish/guarantee it,” not a
required CONTRACT-BROKEN verdict.

Exact T report evidence:

- T/A says the behavior is “not guaranteed”; T/B calls it UNPROVED; and T/D
  expressly declines CONTRACT-BROKEN because the same execution has UB. These
  classifications pass T1.
- T/C says “Documented behavior: CONTRACT-BROKEN”; T/E likewise calls it
  CONTRACT-BROKEN; T/F assigns CONTRACT-BROKEN to the same UB region. Those
  are explicit overstatements, not mere omissions.

Because the plan says a contradiction fails an atom and verdict accuracy is
part of scoring, adjudicated T1 is FAIL for T/C, T/E, and T/F. They still
correctly identify the unsafe obligation and do not launder it, so this is not
a hard error under the preregistered hard-error list.

The same rule applies to mode C. C/D and C/E label the surrogate-panic
postcondition CONTRACT-BROKEN using the same execution that creates an invalid
char and reaches UB. Their C1 atom changes to FAIL; this adds no hard error.

## Adjudicated score matrix

This table applies only the rulings above; every unmentioned raw atom and every
hard-error disposition is preserved.

| Mode | A | B | C | D | E | F |
|---|---:|---:|---:|---:|---:|---:|
| A | 4/4 | 4/4 | 4/4 | 4/4 | 4/4 | 4/4 |
| R | 4/7 HE | 7/7 | 7/7 | 5/7 | 7/7 | 5/7 |
| T | 4/5 HE | 4/5 HE | 4/5 | 5/5 | 3/5 HE | 4/5 |
| P | 5/5 | 5/5 | 5/5 | 5/5 | 5/5 | 5/5 |
| C | 4/5 HE | 5/5 | 4/5 HE | 4/5 | 4/5 | 4/5 HE |
| S | 4/5 HE | 4/5 HE | 4/5 HE | 5/5 | 5/5 | 5/5 |

## Legitimate strictness versus oracle overreach

| Question | Ruling |
|---|---|
| Literal current contracts and current/proposal separation | Legitimately strict. A preferred design cannot reinterpret the old Piece contract or downgrade its finding. |
| A3 enumeration of every possible intent channel | Oracle overreach. Require the contract-over-intent firewall for channels used, not a four-noun checklist. |
| R2 exact behavior, support, no-allocation, internal status, and change authorization | Legitimately strict because every fact is in the request and materially changes the recommendation/compatibility result. |
| R4 mention of a future projection abstraction after selecting specialization | Oracle overreach. The projection option is conditional if offered, not mandatory. |
| R5 explicit rejection of cosmetic/fabricated fixes never proposed | Oracle overreach. Strictly reject such a recommendation or obligation transfer if present. |
| R6 compatibility, proof reduction, and re-audit consequences | Legitimately strict and requested by the design workflow. |
| P2/P3 unknown downstream parties and 1.x directional compatibility | Legitimately strict; these are the central published-contract constraints. |
| P4 an explicit private helper | Oracle overreach. Require a compatible simplification that retains the public audit; accept equivalent techniques. |
| P “readable” interpretation | Genuine source ambiguity. Accept explicit operational or conditional-gap treatments; do not invent an unregistered preference. |
| S4 an explicit unsafe-trait comparison | Oracle overreach when genuine sealing is already correctly chosen. Fail only an unjustified unsafe-trait preference or unenforced boundary. |
| Proposal receiving PROVED before implementation/fresh audit | Legitimately strict and a preregistered hard error. |
| CONTRACT-BROKEN for a witness that necessarily reaches UB | Incorrect verdict, not legitimate strictness. Score the exact-verdict atom false, but do not invent a hard error. |

## Gate application

1. Keep the raw blind files unchanged and report both raw and adjudicated
   matrices.
2. Apply these interpretations symmetrically to treatment and ablation before
   using condition identity. Do not count extra alternative-listing prose as
   treatment success.
3. Compute the preregistered A3 and P4 3/3 treatment gates from their calibrated
   meanings above. A3 tests laundering; P4 tests preservation of the published
   audit and major-version boundary.
4. R4, R5, and S4 pass without a comparison paragraph when the selected design
   itself satisfies the stated constraints and no forbidden alternative is
   recommended.
5. T1/C1 require UNSOUND plus an explicit full-set panic guarantee gap and no
   contradictory CONTRACT-BROKEN label based solely on that UB execution.
   Mislabeling does not mean the report transferred or laundered the safety
   obligation; evaluate the separate no-laundering gate on its own terms.
6. Preserve all proposal-PROVED hard errors. Conditional wording such as
   “implemented exactly as shown” is still certification of a sketch when no
   exact implemented snapshot exists.

This calibration prevents the atom set from rewarding report padding while
retaining strict scoring for facts and separations that the requests and frozen
skill actually require.

## Addendum: mode H rubric calibration

This addendum is limited to H2 and H4. It does not rescore H1 pointer
semantics, H3, H5, or any hard error. The independent H semantic adjudication
establishes that the present raw loop is UNSOUND on Rust 1.70 for a valid empty
slice; that conclusion is used here only to decide what may count as an H4
fallback.

### Raw H scores preserved

| Report | Run | H1 | H2 | H3 | H4 | H5 | Raw total |
|---|---|---|---|---|---|---|---:|
| A | r047 | PASS | PASS | PASS | FAIL | PASS | 4/5 |
| B | r045 | FAIL | FAIL | PASS | FAIL | PASS | 2/5 |
| C | r046 | PASS | FAIL | PASS | FAIL | PASS | 3/5 |
| D | r048 | PASS | FAIL | PASS | FAIL | PASS | 3/5 |
| E | r043 | PASS | FAIL | PASS | PASS | PASS | 4/5 |
| F | r044 | PASS | FAIL | PASS | PASS | PASS | 4/5 |

The raw hard-error and pointer-semantics flags in H.md remain raw evidence and
are not rewritten by this addendum.

### H2: explicit wrapping is enough; an unproposed sum need not be rejected

H2's material requirement is a safe, behavior-preserving candidate whose
arithmetic remains wrapping in every build mode. Plain Iterator::sum with
ordinary u32 addition would not meet that requirement, so a report that
proposes it, recommends it, or leaves the operation ambiguous must reject or
repair it.

When the selected candidate already spells out fold with u32::wrapping_add (or
an equivalent closure) and never proposes plain sum, requiring an additional
warning about sum is a vocabulary/padding test. The H request does not mention
sum, and the treatment reference says not to pad reports with cosmetic or
strictly dominated alternatives. The explicit recurrence itself proves the
required debug/release behavior.

All of r043–r048 select an explicit wrapping-add fold. r047 additionally warns
against sum, but that extra warning should not be the difference between PASS
and FAIL.

Correction: H2 is PASS for reports A–F. Thus B–F change from raw FAIL to
adjudicated PASS; A remains PASS.

### H4: “retain the proved raw loop” is conditional on the loop being proved

The registry's retention language assumes a proved current loop. It cannot
require retaining an implementation once exact-version semantic adjudication
establishes a valid safe-use UB witness. Performance is a binding constraint,
but it cannot authorize shipping an UNSOUND fallback.

Calibrated H4 requires this sequence:

1. prepare and freshly audit an exact behavior-preserving safe candidate;
2. benchmark it under the designated protocol rather than inventing a result;
3. adopt it if the 2% gate passes; and
4. if safe forms fail, investigate a different candidate. A raw-pointer
   fallback is acceptable only after the known defect is repaired and that
   exact source receives local proofs, fresh audit, and benchmark evidence.

r045 (report B) gives exactly that conditional path. It refuses to ship the
present loop, tries safe iterator/for-loop forms first, and, only if none meets
the gate, proposes benchmarking a pointer fallback that returns immediately
for an empty slice, carries complete local pointer proofs, and is audited as an
exact implementation. Its use of the present code solely as a benchmark
baseline does not retain it as a releasable design. H4 changes from FAIL to
PASS.

r043 and r044 (reports E and F) explicitly say to retain the current loop with
comments if the safe benchmark fails. Comments cannot repair its Rust 1.70
empty-slice UB, so H4 changes from PASS to FAIL for both.

r046 and r048 (reports C and D) likewise retain the current unsound loop and
also carry their previously recorded proposal/fresh-audit defects; H4 remains
FAIL. r047 (report A) would keep unsafe code after closing its alleged
slice-span premise, but that premise does not repair the empty add(0) defect
and it lacks the required fresh exact-source boundary; H4 remains FAIL.

### H2/H4-only adjusted matrix

All other raw atom values and all hard-error flags are held fixed here.

| Report | Run | Adjusted H2 | Adjusted H4 | H2/H4-adjusted total |
|---|---|---|---|---:|
| A | r047 | PASS | FAIL | 4/5 |
| B | r045 | PASS | PASS | 4/5 |
| C | r046 | PASS | FAIL | 4/5 |
| D | r048 | PASS | FAIL | 4/5 |
| E | r043 | PASS | FAIL | 4/5 |
| F | r044 | PASS | FAIL | 4/5 |

Gate interpretation:

- H2 tests preservation of wrapping arithmetic, not whether the report names a
  dominated operation it never selected.
- H4 may retain the present raw implementation only if semantic adjudication
  actually proves it over the requested support set. When it is UNSOUND,
  conditional retention must mean a repaired, separately audited candidate,
  as in r045—not the same source plus comments.

## Addendum: N2 witness granularity

The raw N matrix is preserved: report A/r051 received 4/5 with N2 FAIL, while
reports B–F received 5/5; no N report had a hard error.

The registry names two manifestations of the same detached-output-lifetime
defect: two retained results from get_mut, and a retained get result followed
by get_mut. These are valuable discovery examples, but N2 should not require
two separate code witnesses when equivalent reasoning proves the shared defect
and covers both accessors.

Calibrated N2 passes when a report supplies:

1. at least one fully concrete, wholly safe execution reaching UB;
2. an UNSOUND verdict for the exact implemented snapshot;
3. explicit root-cause reasoning that applies to both get and get_mut rather
   than treating the demonstrated sequence as an isolated bug; and
4. a repair that binds both methods' output lifetimes to their receiver borrows
   (or an equivalent design eliminating the defect in both).

Both explicit witnesses also pass. One witness alone fails only when the other
accessor or its shared lifetime mechanism is left unanalyzed.

r051 meets the equivalent-reasoning form. Its safe shared-then-mutable example
is a complete UB witness. It inventories both methods, says PhantomData and the
constructor do not tie references returned by “the accessors” to receiver
borrows, states that both methods return references through the unchanged
pointer, and explains that the repeatable detached-'a capability cannot remain
on both safe accessors. Its proposed reference-backed design receiver-binds
both get and get_mut, with the raw-pointer fallback required to do the same.

Requiring r051 to add the mechanically analogous two-get_mut snippet would
reward report padding rather than recover a missing soundness proposition. One
valid safe UB witness already establishes UNSOUND; the cross-method analysis
and two-method repair establish that neither surface was overlooked.

Correction: report A/r051 changes from N2 FAIL to PASS and from raw 4/5 to
adjudicated 5/5. Reports B–F remain 5/5, raw scores remain recorded unchanged,
and no hard-error disposition changes.
