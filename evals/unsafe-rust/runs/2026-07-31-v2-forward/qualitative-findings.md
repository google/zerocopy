# V2 Forward Evaluation: Qualitative Findings

This is post-unblinding interpretation of the frozen evaluation. It does not
amend the packages, fixtures, oracle, scoring rules, gates, canonical blind
matrices, or mechanically generated [`results.md`](results.md).

## Bottom line

V2 failed its preregistered release gates. It produced 16 failed atom cells and
five hard errors. Those failures are concentrated rather than diffuse:

- Mode D accounts for 12 of 16 failed atom cells and four of five hard errors.
- Mode H accounts for the remaining hard error and one failed atom cell.
- Modes A and N account for the remaining three failed atom cells without hard
  errors.
- Modes U, V, I, T, C, and P pass every V2 atom; no V2 report launders an
  unimplemented proposal into a proved artifact.

The evidence supports the narrower conclusion that V2 often elicits excellent
proof-grade reviews and that several intended disciplines work reliably on
these fixtures. It does not support declaring V2 gate-ready, broadly superior
to V1, or reliable enough for a zero-miss standard.

## Failure analysis

### D: support-domain recovery was not itself proved

The two controlling policies both describe stable Rust releases from 1.79.0
through 1.82.0 inclusive. Four V2 reports translated that interval into
`{1.79.0, 1.80.0, 1.81.0, 1.82.0}`, omitting the stable patch release 1.80.1.
They then proved the source over that smaller set and asserted closure over the
conservative policy union. Only [`r124`](reports/r124.md) retained 1.80.1 and
passed D1--D3.

This is not primarily an unsafe-operation proof failure. The reports correctly
handled the policy conflict, rejected CI and the developer toolchain pin as
support authority, and gave a valid bounds proof for each configuration they
considered. The defect occurred earlier: policy prose was converted into a
formal domain without proving that the conversion was lossless. Exhaustive
coverage over a malformed domain is not exhaustive coverage of the requested
theorem.

The current package already requires a precise supported predicate, a
conservative union, exact-version premise applicability, and universal or
exhaustive configuration closure. The four-of-five recurrence nevertheless
shows that those rules do not operationalize domain recovery reliably enough.
The next revision should make recovery of the quantified domain an explicit
proof obligation:

1. Preserve ranges, unions, exclusions, and conditional structure symbolically
   unless a finite member inventory is independently justified.
2. Treat an enumeration as a lemma requiring evidence that it is extensionally
   equal to the controlling predicate.
3. Prove the implementation parametrically over the symbolic predicate, or
   prove premise coverage for every justified member or exhaustive partition.
4. Falsify coverage with interior and boundary members before certifying it.
   Patch releases are one example, not the rule itself.
5. If exact membership or equivalence cannot be established, preserve the
   symbolic domain and leave any unsupported region `UNPROVED`.

This is the highest-priority V3 change and deserves multiple new fixtures with
different interval, union, exclusion, and moving-policy shapes.

### H: an existential UB proof was mistaken for a universal proof gap

[`r021`](reports/r021.md) states that Rust 1.70 `pointer::add` requires the
start and result to be within or one-past the same allocation, that a valid
empty slice may use an aligned pointer not attached to an allocation, and that
Rust 1.70 has no zero-offset exemption. Those premises already entail a valid
safe call whose executed `add(0)` violates its contract. The report nevertheless
declares the result `UNPROVED` and asks for a proposition saying `add(0)` is
defined for every empty-slice pointer. It therefore tries to close the
universal soundness proof after it has already assembled an existential
refutation of that proof.

The skill already distinguishes `UNPROVED` from `UNSOUND`, requires indirect
multi-premise derivation, and says one valid UB execution refutes a safe API's
universal soundness claim. This is primarily a stochastic proof-composition and
verdict-calibration failure, not an absent concept. A compact final
counterexample-closure check may make the existing model more reliable:

- Is the proposed input or state a valid in-scope use?
- Is the relevant operation executed on that path?
- Which exact contract clause is false at that operation?
- Does the applicable authority make violating that clause UB?

When all four answers are proved, the scoped verdict is `UNSOUND`; no theorem
about every member of the input class is needed. When only the universal proof
fails and no valid counterexample is proved, the verdict remains `UNPROVED`.

### A: sampled releases were promoted to an interval theorem

[`r019`](reports/r019.md) and [`r126`](reports/r126.md) correctly distinguish
the false literal `Piece` contract from the validity of the projected `u32`.
Their A2 failures arise because they additionally claim `PROVED` soundness over
the stable 1.70.0--1.97.1 interval while relying on endpoint or sparse sampled
documentation and explicitly admitting no compatibility premise. The three
passing V2 reports prove the exact Rust 1.70 region and leave the unproved
remainder visible.

V2 already forbids this interpolation, so the failures show adherence
unreliability rather than a missing semantic rule. A positive-verdict
certification step should require every multi-release `PROVED` region to name
one of:

- an applicable proposition-preserving compatibility premise;
- a valid parametric proof over the entire region; or
- an exhaustive partition whose every member or class has applicable evidence.

An audit cutoff bounds a claim; it does not prove continuity up to that cutoff.
Endpoint samples prove endpoints, not the interval between them.

This result also exposed a scoring-design issue. A2's central proposition is
contract-versus-soundness separation, which both reports perform correctly;
the failed interval scope is separately material to their affirmative verdict.
A future oracle should score those as separate atoms, or pin this unchanged
control to one exact Rust version so an unrelated scope error does not obscure
the intended control.

### N: one independent alias route was omitted

[`r067`](reports/r067.md) correctly reports the current snapshot `UNSOUND`,
fully proves the retained-`get`/later-`get_mut` witness, identifies the
receiver-unbound `'a` output lifetimes as the enabling defect, repairs both
accessor signatures, and withholds a verdict from the proposal. It does not
explicitly instantiate the second oracle-required route: two simultaneously
live results from repeated `get_mut` calls. The adjudicator declined to infer
that route from the report's generic discussion of reusable capability.

This is a narrow completeness omission with genuine shorthand-granularity
ambiguity, not evidence that the skill taught the wrong model. One witness is
enough to refute aggregate soundness, but one witness does not necessarily
complete an exhaustive audit of independently failing surfaces or composition
routes. No skill change should be made for N alone. A future oracle should:

- split the two witness routes into separate atoms;
- preregister what explicit analogous reasoning is sufficient; and
- score complete obligation/surface coverage without imposing an impossible
  requirement to enumerate every conceivable client program.

If a larger targeted replication shows recurring omissions, a general
reporting rule may require auditors to continue disposing of independently
failing obligation sites after the first witness establishes `UNSOUND`.

## What worked

- U, T, and C apply the whole-execution UB/postcondition rule in every V2
  report. A UB-containing execution is not used as a defined behavioral
  counterexample.
- V partitions an exact semantic boundary between Rust 1.79 and 1.80 correctly
  in every condition and V2 report.
- I rejects producer-precondition promotion, follows both producers, and
  derives the safe UB witness in every condition and V2 report.
- T, C, and H keep current-source findings, redesign proof plans, performance
  evidence, and implemented-artifact verdicts separate. V2 has zero proposal
  laundering.
- P preserves a published contract in the face of incomplete consumer search
  and separates compatible internal simplification from contract weakening.
- Passing reports frequently reconstruct material missing safety proofs and
  expose the reconstruction rather than silently accepting deficient comments.

These are capability results on the frozen fixtures, not a statistical proof
that the skill caused every success. Several modes are at ceiling in all three
conditions.

## Comparative interpretation and limitations

V2 versus V1 is the preregistered primary comparison. Results are mixed: V2
improves U2, T2, H1, and P1 by one report each, improves D2 and D3 by one, but
regresses D1 by one, A2 by two, and N1 by one. V and I are ceiling results in
all conditions. The V1 core ablation is only a historical bridge and does not
isolate V2's changes; its proposal-laundering failures in T and C support the
value of the full abstraction-design material but cannot identify which V2
wording caused later outcomes.

Interpret these comparisons cautiously:

- five reports per cell are an engineering screen, not a power analysis;
- report sampling is stochastic and no fixed model seed or durable model
  identity was available;
- heterogeneous modes must not be pooled into one performance estimate;
- ceiling effects hide possible differences; and
- some atom boundaries produced genuine scorer disagreement.

The zero-miss preregistered gate is intentionally demanding. Its failure is
conclusive for release gating even where causal attribution is uncertain.

## Recommended sequence

1. Preserve this V2 run unchanged as a failed preregistered evaluation.
2. Design V3 holistically around theorem-domain recovery and final
   certification, integrating the D, H, and A lessons without adding
   fixture-specific hazard trivia.
3. Refine the A and N oracle atoms before using them again.
4. Freeze V3 separately, then run targeted confirmatory suites for support-set
   translation, existential-refutation closure, and multi-release scope, plus
   unchanged regression controls.
5. Only after targeted confirmation should a broader fresh-agent audit suite
   be used as the next release gate.

The requested final process retrospective remains deferred until all skill and
meta-file revisions and all evaluation rounds are complete.
