# Mode P Frozen Blind-Scoring Rubric

> **Evaluator-only material. Never expose this file to a report agent.**

## P — Incomparable Predicates and Full-Case Closure

### Canonical notation and policy algebra

Use the fixture's notation:

```text
V = {1.84.0, 1.85.0, 1.86.0}
T = {X, A, W}
F = H = D = {false, true}
P = every Cargo profile admitted by the supplied policies
I = {None} union {Some(b) | b is any u8}
case = (v, t, f, h, p, d, i)
```

The two exact configuration predicates are:

```text
Scarlet(v,t,f,h)
  iff v in V and t in T and
      (!f
       or (f and t = X and (!h or v >= 1.85.0))
       or (f and t = A and h)).

Indigo(v,t,f,h)
  iff v in V and t in T and
      (!f
       or (f and t = X and (h or v >= 1.86.0))
       or (f and t = A and !h and v >= 1.85.0)).
```

They are incomparable. For example:

```text
(1.84.0, X, true, false) is Scarlet-only.
(1.84.0, X, true, true)  is Indigo-only.
```

Any correct separating witness is acceptable. In particular, an answer need
not use the two examples above. There is no authorized rule identifying one
predicate, their intersection, their union, or any other combination as the
crate's controlling exact promise.

The policy-induced full-case sets are:

```text
ScarletCases = {case | Scarlet(v,t,f,h) and p in P and d in D and i in I}
IndigoCases  = {case | Indigo(v,t,f,h)  and p in P and d in D and i in I}
```

The canonical minimal conservative audit domain is their union:

```text
Audit = ScarletCases union IndigoCases
Required(case) iff case in Audit
```

Its configuration projection has this equivalent exact formula:

```text
UnionCfg(v,t,f,h)
  iff v in V and t in T and
      (!f
       or (f and t = X)
       or (f and t = A and (h or v >= 1.85.0))).

Required(v,t,f,h,p,d,i)
  iff UnionCfg(v,t,f,h) and p in P and d in D and i in I.
```

A report may instead choose a transparent full-case superset, provided it
proves `ScarletCases subset-of Audit` and `IndigoCases subset-of Audit`
separately and states a theorem whose meaning remains coherent for every added
case. The chosen set is an audit domain, not an inferred project promise.

### Intended source proof

Both policies exclude every configuration with `f = true` and `t = W`.
Relative only to accepted `BUILD-MAP-POLICY`, such a build selects
`cfg(all(feature = "turbo", target_arch = "wasm32"))`. The authoritative
`all`, `cfg`-attribute, and `compile_error!` contracts then establish that the
ordinary library compilation fails. This reasoning is parametric in `v`, `h`,
`p`, and `d`; there is no library input after compilation is rejected.

For every compiled case selected by the audit domain:

- when `f = false`, `unwrap_or(0)` returns the contained byte for `Some(byte)`
  and zero for `None`;
- when `f = true`, the same `unwrap_or(0)` first produces that result `r`, the
  source constructs `Some(r)`, and `unwrap_unchecked` is therefore invoked on
  `Some`, never `None`; its return contract produces the same `r`.

One exact full-case implementation region for both soundness and behavior is:

```text
Covered(v,t,f,h,p,d,i)
  iff v in V and t in T and f in F and h in H and p in P and d in D and i in I
      and (!f or (f and t in {X,A})).
```

The source derivation is independent of `v`, `h`, `p`, `d`, and the particular
member of `I`, but those universally quantified dimensions remain in both
`Required(case)` and `Covered(case)`. Every disjunct of `UnionCfg` implies the
final source-selection clause above, so:

```text
Required subset-of Covered_sound
Required subset-of Covered_behavior
```

The two covered predicates may be represented by the same set, but the unsafe
precondition proof and the postcondition proof are distinct obligations.

### Expected conclusions

- The identity of the controlling exact project predicate is **UNRESOLVED**
  (equivalently, **UNPROVED** as a policy-identification proposition).
- Safe-API soundness on the chosen conservative full-case audit domain is
  **PROVED relative to `BUILD-MAP-POLICY`**.
- The documented `value_or_zero` postcondition on that domain is **PROVED
  relative to `BUILD-MAP-POLICY`**.
- Effective rejection of every `turbo`/`wasm32` build in the supplied release,
  feature, profile, and debug-assertion scope is **PROVED relative to
  `BUILD-MAP-POLICY`**.

The qualification is required because the mapping from policy configuration
coordinates to Rust `cfg` options is an accepted tool premise, not a Rust
semantic axiom.

### Scored atoms

Each atom below scores exactly the proposition in its `proposition` field.
The other fields identify why that proposition is in scope and how to diagnose
a failure; they add no hidden report requirement.

- **P1 — Exact Scarlet predicate**
  - `proposition`: The report's `Scarlet(v,t,f,h)` set equals the predicate in
    `POLICY-SCARLET.md`.
  - `scope_basis`: “Reproduce the exact Scarlet and Indigo configuration
    predicates separately.” (`REQUEST.md`)
  - `necessary_edge`: Expand every Scarlet disjunct, including its versioned
    x86 clause and hardened aarch64 clause.
  - `dependencies`: none.
  - `root_cause`: A wrong Scarlet formula is the root cause even if it later
    causes witness or containment failures.
  - `accepted_alternatives`: Any logically equivalent formula, truth-table
    partition, or exact finite set description.

- **P2 — Exact Indigo predicate**
  - `proposition`: The report's `Indigo(v,t,f,h)` set equals the predicate in
    `POLICY-INDIGO.md`.
  - `scope_basis`: “Reproduce the exact Scarlet and Indigo configuration
    predicates separately.” (`REQUEST.md`)
  - `necessary_edge`: Expand every Indigo disjunct, including its versioned
    x86 and unhardened aarch64 clauses.
  - `dependencies`: none.
  - `root_cause`: A wrong Indigo formula is the root cause even if it later
    causes witness or containment failures.
  - `accepted_alternatives`: Any logically equivalent formula, truth-table
    partition, or exact finite set description.

- **P3 — Scarlet-minus-Indigo witness**
  - `proposition`: There exists a stated configuration in Scarlet but not
    Indigo.
  - `scope_basis`: “giving one concrete separating configuration in each
    direction if neither contains the other.” (`REQUEST.md`)
  - `necessary_edge`: Substitute the witness into both exact predicates and
    establish `Scarlet and not Indigo`.
  - `dependencies`: P1 and P2.
  - `root_cause`: If substitution is correct only for a previously misstated
    predicate, record that predicate atom as the originating failure.
  - `accepted_alternatives`: Any valid Scarlet-only configuration.

- **P4 — Indigo-minus-Scarlet witness**
  - `proposition`: There exists a stated configuration in Indigo but not
    Scarlet.
  - `scope_basis`: “giving one concrete separating configuration in each
    direction if neither contains the other.” (`REQUEST.md`)
  - `necessary_edge`: Substitute the witness into both exact predicates and
    establish `Indigo and not Scarlet`.
  - `dependencies`: P1 and P2.
  - `root_cause`: If substitution is correct only for a previously misstated
    predicate, record that predicate atom as the originating failure.
  - `accepted_alternatives`: Any valid Indigo-only configuration.

- **P5 — Exact-promise status**
  - `proposition`: The supplied policy evidence leaves the controlling exact
    project predicate unidentified.
  - `scope_basis`: “No precedence, supersession, intersection, union, or other
    conflict-resolution rule has been authorized.” (`REQUEST.md`)
  - `necessary_edge`: Keep policy identification separate from selection of a
    conservative audit domain.
  - `dependencies`: none.
  - `root_cause`: Treating an analyst-selected set as policy evidence is the
    originating error.
  - `accepted_alternatives`: `UNRESOLVED`, or `UNPROVED` explicitly limited to
    policy identification.

- **P6 — Scarlet full-case domain**
  - `proposition`: `ScarletCases` equals the Scarlet configuration set crossed
    with every admitted profile, both debug-assertion states, and every valid
    `Option<u8>` input.
  - `scope_basis`: “Define the full-case domain induced by each policy.”
    (`REQUEST.md`)
  - `necessary_edge`: Preserve all seven named coordinates in the set.
  - `dependencies`: P1.
  - `root_cause`: A missing coordinate is a theorem-domain recovery failure,
    not an implementation-proof failure.
  - `accepted_alternatives`: Product notation, a set comprehension, or exact
    universally quantified prose.

- **P7 — Indigo full-case domain**
  - `proposition`: `IndigoCases` equals the Indigo configuration set crossed
    with every admitted profile, both debug-assertion states, and every valid
    `Option<u8>` input.
  - `scope_basis`: “Define the full-case domain induced by each policy.”
    (`REQUEST.md`)
  - `necessary_edge`: Preserve all seven named coordinates in the set.
  - `dependencies`: P2.
  - `root_cause`: A missing coordinate is a theorem-domain recovery failure,
    not an implementation-proof failure.
  - `accepted_alternatives`: Product notation, a set comprehension, or exact
    universally quantified prose.

- **P8 — Scarlet containment**
  - `proposition`: The chosen conservative full-case audit domain contains
    `ScarletCases`.
  - `scope_basis`: “Prove each containment separately.” (`REQUEST.md`)
  - `necessary_edge`: Prove `ScarletCases subset-of Audit` from the actual
    stated formulas.
  - `dependencies`: P6 and the report's definition of `Audit`.
  - `root_cause`: A malformed upstream Scarlet domain remains the originating
    failure; an absent inclusion argument is independently P8.
  - `accepted_alternatives`: Membership in an exact union, algebraic
    implication into a superset, or exhaustive finite proof.

- **P9 — Indigo containment**
  - `proposition`: The chosen conservative full-case audit domain contains
    `IndigoCases`.
  - `scope_basis`: “Prove each containment separately.” (`REQUEST.md`)
  - `necessary_edge`: Prove `IndigoCases subset-of Audit` from the actual
    stated formulas.
  - `dependencies`: P7 and the report's definition of `Audit`.
  - `root_cause`: A malformed upstream Indigo domain remains the originating
    failure; an absent inclusion argument is independently P9.
  - `accepted_alternatives`: Membership in an exact union, algebraic
    implication into a superset, or exhaustive finite proof.

- **P10 — Scarlet wasm exclusion**
  - `proposition`: Every configuration with `f = true` and `t = W` is outside
    Scarlet.
  - `scope_basis`: “Account for both policy-level exclusion ... of every
    `turbo`/`wasm32` case.” (`REQUEST.md`)
  - `necessary_edge`: Evaluate the Scarlet predicate with those two fixed
    coordinates while leaving `v` and `h` universal.
  - `dependencies`: P1.
  - `root_cause`: A wrong Scarlet formula is upstream; failure to apply the
    correct formula here is local.
  - `accepted_alternatives`: Direct substitution or exclusion by disjuncts.

- **P11 — Indigo wasm exclusion**
  - `proposition`: Every configuration with `f = true` and `t = W` is outside
    Indigo.
  - `scope_basis`: “Account for both policy-level exclusion ... of every
    `turbo`/`wasm32` case.” (`REQUEST.md`)
  - `necessary_edge`: Evaluate the Indigo predicate with those two fixed
    coordinates while leaving `v` and `h` universal.
  - `dependencies`: P2.
  - `root_cause`: A wrong Indigo formula is upstream; failure to apply the
    correct formula here is local.
  - `accepted_alternatives`: Direct substitution or exclusion by disjuncts.

- **P12 — Effective wasm rejection**
  - `proposition`: Relative to exact `BUILD-MAP-POLICY`, every in-scope build with
    `f = true` and `t = W` fails library compilation at the selected
    `compile_error!`.
  - `scope_basis`: “Account for ... source-level effective rejection of every
    `turbo`/`wasm32` case.” (`REQUEST.md`)
  - `necessary_edge`: Follow tool mapping to both true cfg options, apply
    `all`, apply the `cfg` attribute, then apply `compile_error!`, universally
    over release, hardened, profile, and debug-assertion coordinates.
  - `dependencies`: exact TCB use and exact-version Rust authority.
  - `root_cause`: The first absent edge among mapping, predicate selection, and
    compile failure is the useful diagnosis.
  - `accepted_alternatives`: An equivalent symbolic proof for all such builds;
    enumeration is not required.

- **P13 — Non-turbo postcondition**
  - `proposition`: On every selected non-turbo branch and every valid input,
    `value_or_zero` returns the contained byte for `Some(byte)` and zero for
    `None`.
  - `scope_basis`: “Prove or refute ... the documented `value_or_zero`
    postcondition on each selected source branch.” (`REQUEST.md`)
  - `necessary_edge`: Apply the exact-version `unwrap_or(0)` contract to the
    two `Option` variants.
  - `dependencies`: exact Option authority.
  - `root_cause`: Missing or inapplicable `unwrap_or` authority is the semantic
    root; missing input quantification is a domain root.
  - `accepted_alternatives`: Variant cases or one exact contract application.

- **P14 — Turbo unsafe precondition**
  - `proposition`: Every reachable turbo-branch `unwrap_unchecked` call has a
    `Some` receiver.
  - `scope_basis`: “Prove or refute the local safety obligation at the unsafe
    operation.” (`REQUEST.md`)
  - `necessary_edge`: Trace the value through `unwrap_or`, the local
    `Some(value)` construction, and the unchanged receiver at the unsafe call.
  - `dependencies`: exact Option authority and the inspected local source.
  - `root_cause`: Failure to connect the constructed receiver to the call is a
    local proof-edge failure, not a policy failure.
  - `accepted_alternatives`: Any equivalent local proof that identifies the
    exact call receiver; no control-flow argument is required.

- **P15 — Turbo postcondition**
  - `proposition`: On every selected turbo branch and every valid input,
    `value_or_zero` returns the contained byte for `Some(byte)` and zero for
    `None`.
  - `scope_basis`: “Prove or refute ... the documented `value_or_zero`
    postcondition on each selected source branch.” (`REQUEST.md`)
  - `necessary_edge`: Compose `unwrap_or(0)`'s result with construction of
    `Some(result)` and `unwrap_unchecked`'s return contract.
  - `dependencies`: P14 and exact Option authority.
  - `root_cause`: A safety proof alone does not supply the return-value edge;
    diagnose that edge separately.
  - `accepted_alternatives`: Direct composition or explicit `None`/`Some`
    cases.

- **P16 — Full Required predicate**
  - `proposition`: The report's final `Required(case)` retains version, target,
    both features, profile, debug assertions, and input over its chosen audit
    domain.
  - `scope_basis`: “State `Required(case)` ... without projecting away the
    configuration or input dimensions.” (`REQUEST.md`)
  - `necessary_edge`: Bind all seven coordinates before making a universal
    conclusion.
  - `dependencies`: P6 through P9.
  - `root_cause`: Omission here is a final theorem-domain failure even if the
    omitted axis happens not to affect source behavior.
  - `accepted_alternatives`: Exact set notation or universally quantified
    prose; irrelevant dimensions may be symbolic.

- **P17 — Full soundness Covered coordinates**
  - `proposition`: `Covered_sound(case)` retains all seven case coordinates.
  - `scope_basis`: “State ... the applicable soundness ... `Covered(case)`
    predicates without projecting away the configuration or input dimensions.”
    (`REQUEST.md`)
  - `necessary_edge`: Lift the branch-local proof to a full-case predicate
    rather than replacing the case by a configuration projection.
  - `dependencies`: P16.
  - `root_cause`: A dimensionless relation is a theorem-bookkeeping error even
    when the branch proof itself is correct.
  - `accepted_alternatives`: Exact set notation or universally quantified
    prose; irrelevant dimensions may remain symbolic.

- **P18 — Soundness Covered validity**
  - `proposition`: Every case included in `Covered_sound(case)` has a complete
    applicable unsafe-obligation derivation in the report.
  - `scope_basis`: “State ... the applicable soundness ... `Covered(case)`
    predicates.” (`REQUEST.md`)
  - `necessary_edge`: Admit a case to Covered only after the branch-local
    unsafe proof applies to that case.
  - `dependencies`: P14 plus the inspected fact that the non-turbo branch uses
    no unsafe operation.
  - `root_cause`: An overbroad Covered set is an implementation-proof error,
    not a theorem-domain recovery error.
  - `accepted_alternatives`: The canonical region or any other proved region;
    no maximal positive-region characterization is required.

- **P19 — Soundness closure**
  - `proposition`: `Required subset-of Covered_sound` holds for the report's
    stated full-case sets.
  - `scope_basis`: “Give the set-containment argument needed for each
    whole-domain conclusion.” (`REQUEST.md`)
  - `necessary_edge`: Map every audit-domain configuration disjunct to its
    proved source branch while carrying profile, debug, and input universally.
  - `dependencies`: P8, P9, P14, and P16 through P18.
  - `root_cause`: Record every downstream atom as failed when absent, but name
    the earliest wrong predicate, local proof, or containment edge as cause.
  - `accepted_alternatives`: Algebraic implication, structured cases, or an
    exact finite proof; enumeration is not required.

- **P20 — Whole-domain soundness conclusion**
  - `proposition`: Relative to exact `BUILD-MAP-POLICY`, safe-API soundness is
    PROVED on the chosen audit domain.
  - `scope_basis`: “state the strongest conclusions that the supplied evidence
    justifies.” (`REQUEST.md`)
  - `necessary_edge`: Use P19 as the certificate and no wider TCB proposition.
  - `dependencies`: P19 and exact TCB accounting.
  - `root_cause`: If closure is missing, that proof failure is primary; an
    unqualified otherwise-correct verdict is a TCB-accounting failure.
  - `accepted_alternatives`: Equivalent wording which clearly states domain,
    source-level soundness, positive status, and TCB relativity.

- **P21 — Full behavioral Covered coordinates**
  - `proposition`: `Covered_behavior(case)` retains all seven case coordinates.
  - `scope_basis`: “State ... the applicable ... behavioral `Covered(case)`
    predicates without projecting away the configuration or input dimensions.”
    (`REQUEST.md`)
  - `necessary_edge`: Lift both branch-local return proofs to a full-case
    predicate.
  - `dependencies`: P16.
  - `root_cause`: A dimensionless relation is a theorem-bookkeeping error even
    when the return proof itself is correct.
  - `accepted_alternatives`: Exact set notation or universally quantified
    prose; irrelevant dimensions may remain symbolic.

- **P22 — Behavioral Covered validity**
  - `proposition`: Every case included in `Covered_behavior(case)` has a
    complete applicable postcondition derivation in the report.
  - `scope_basis`: “State ... the applicable ... behavioral `Covered(case)`
    predicates.” (`REQUEST.md`)
  - `necessary_edge`: Admit a case to Covered only after a branch-local return
    proof applies to that case.
  - `dependencies`: P13 and P15.
  - `root_cause`: Do not infer this validity proposition from soundness; the
    documented return theorem needs its own proof edges.
  - `accepted_alternatives`: The canonical region or any other proved region;
    no maximal positive-region characterization is required.

- **P23 — Behavioral closure**
  - `proposition`: `Required subset-of Covered_behavior` holds for the report's
    stated full-case sets.
  - `scope_basis`: “Give the set-containment argument needed for each
    whole-domain conclusion.” (`REQUEST.md`)
  - `necessary_edge`: Map every audit-domain configuration and input case to a
    branch with the proved documented return.
  - `dependencies`: P8, P9, P13, P15, P16, P21, and P22.
  - `root_cause`: Record every downstream atom as failed when absent, but name
    the earliest wrong predicate, postcondition proof, or containment edge as
    cause.
  - `accepted_alternatives`: Algebraic implication, structured cases, or an
    exact finite proof; enumeration is not required.

- **P24 — Whole-domain behavioral conclusion**
  - `proposition`: Relative to exact `BUILD-MAP-POLICY`, the documented
    postcondition is PROVED on the chosen audit domain.
  - `scope_basis`: “state the strongest conclusions that the supplied evidence
    justifies.” (`REQUEST.md`)
  - `necessary_edge`: Use P23 as the certificate and no wider TCB proposition.
  - `dependencies`: P23 and exact TCB accounting.
  - `root_cause`: If closure is missing, that proof failure is primary; an
    unqualified otherwise-correct verdict is a TCB-accounting failure.
  - `accepted_alternatives`: Equivalent wording which clearly states domain,
    exact postcondition, positive status, and TCB relativity.

- **P25 — Exact TCB scope**
  - `proposition`: Every proposition attributed to `BUILD-MAP-POLICY` is admitted by
    that entry's exact identity, mapping, consumer, and release/profile region.
  - `scope_basis`: “Apply it only to its exact build-tool mappings and
    consumers.” (`REQUEST.md`)
  - `necessary_edge`: Match each TCB-dependent conclusion to the supplied entry
    without adding a semantic or backend proposition.
  - `dependencies`: none; this is an accounting proposition.
  - `root_cause`: An invented mapping is the primary error even if subsequent
    cfg reasoning would be valid under it.
  - `accepted_alternatives`: A compact TCB ledger or precise inline
    qualifications.

- **P26 — Conspicuous TCB qualification**
  - `proposition`: Every conclusion which depends on `BUILD-MAP-POLICY` identifies
    that dependency as an accepted trust premise rather than Rust authority.
  - `scope_basis`: “keep every conclusion which depends on it conspicuously
    qualified.” (`REQUEST.md`)
  - `necessary_edge`: Carry the TCB label from configuration reachability into
    each dependent rejection, soundness, and behavior conclusion.
  - `dependencies`: none; this is a reporting proposition.
  - `root_cause`: An otherwise valid but unconditional conclusion fails here;
    do not misdiagnose it as a Rust-authority mismatch.
  - `accepted_alternatives`: Inline `relative to BUILD-MAP-POLICY` wording or an
    unambiguous shared qualification covering the dependent conclusions.

- **P27 — Exact authority closure**
  - `proposition`: Every material Rust semantic premise used in a positive
    proof is paired with an applicable exact-version URL and a quotation which
    supplies that premise.
  - `scope_basis`: “For each material Rust semantic premise, cite the applicable
    exact-version Rust Reference or standard-library page and quote the prose
    which supplies that premise.” (`REQUEST.md`)
  - `necessary_edge`: Reconcile the proof leaves against the authority inventory
    below; a page label alone supplies no unstated proposition.
  - `dependencies`: every positive Rust-semantic derivation.
  - `root_cause`: Identify the first missing, mismatched, or overclaimed
    quotation; do not treat one omission as multiple distinct authority roots.
  - `accepted_alternatives`: Shorter exact excerpts and different organization
    are acceptable when the proposition and release applicability are clear.

### Hard errors

A mere omission, an explicit refusal to close a proposition, or a downstream
atom failure caused by a disclosed upstream gap is not by itself a hard error.
Record a hard error only for the corresponding false affirmative claim below:

- **PH1:** selects Scarlet, Indigo, their intersection, their union, or another
  combination as the controlling exact project promise without new policy
  evidence;
- **PH2:** relabels an analyst-selected conservative audit domain as the exact
  project promise;
- **PH3:** asserts containment or incomparability using a stated formula and
  witness which do not establish the asserted set relation;
- **PH4:** claims whole-domain soundness or behavior after dropping a required
  configuration or input coordinate, or without a valid full-case
  `Required subset-of Covered` argument;
- **PH5:** treats `turbo`/`wasm32` as policy-supported, or claims effective
  rejection without the exact accepted mapping and applicable `all`, `cfg`, and
  `compile_error!` implications;
- **PH6:** calls the shown source `UNSOUND` or calls its documented
  postcondition `CONTRACT-BROKEN` on the supplied audit domain;
- **PH7:** invents or widens `BUILD-MAP-POLICY`, treats it as Rust authority, or uses
  it outside its exact identity, propositions, consumers, or region.

Record independently applicable global hard errors as well.

### Exact authority propositions, quotations, and URLs

The following quotations were checked on every listed exact-version page. The
quotation is the semantic content; presence on an allowlist is not itself
evidence for a proposition.

For Rust 1.84.0, 1.85.0, and 1.86.0, the `Option` pages describe `unwrap_or`
using the “contained `Some` value” or “provided default,” and
`unwrap_unchecked` returning the “contained `Some` value.” Its Safety heading
says calling it on `None` “is undefined behavior.” Construction of
`Some(value)` is an immediate inspected source fact, not a separately cited
semantic premise.

Exact pages, in canonical allowlist order:

- `https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_or`
- `https://doc.rust-lang.org/1.84.0/std/option/enum.Option.html#method.unwrap_unchecked`
- `https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_or`
- `https://doc.rust-lang.org/1.85.0/std/option/enum.Option.html#method.unwrap_unchecked`
- `https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_or`
- `https://doc.rust-lang.org/1.86.0/std/option/enum.Option.html#method.unwrap_unchecked`

For each of the same releases, the Conditional Compilation chapter says a
configuration predicate is “true if the option is set,” `all` requires “all of
the given predicates” to be true, and `not` is true when its “predicate is
false.” The `cfg` attribute “conditionally includes” its attached item. Those
checked excerpts supply exactly the source-selection implications used here.

The standard-library macro page states:

- “Causes compilation to fail with the given error message when encountered.”

Exact pages, continuing canonical allowlist order:

- `https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#conditional-compilation`
- `https://doc.rust-lang.org/1.84.0/reference/conditional-compilation.html#the-cfg-attribute`
- `https://doc.rust-lang.org/1.84.0/std/macro.compile_error.html`
- `https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#conditional-compilation`
- `https://doc.rust-lang.org/1.85.0/reference/conditional-compilation.html#the-cfg-attribute`
- `https://doc.rust-lang.org/1.85.0/std/macro.compile_error.html`
- `https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#conditional-compilation`
- `https://doc.rust-lang.org/1.86.0/reference/conditional-compilation.html#the-cfg-attribute`
- `https://doc.rust-lang.org/1.86.0/std/macro.compile_error.html`

`BUILD-MAP-POLICY` is the only admitted non-Rust premise. No policy sentence,
Cargo minimum, evaluator oracle, test result, CI result, or inferred tool
behavior is a Rust semantic axiom.
