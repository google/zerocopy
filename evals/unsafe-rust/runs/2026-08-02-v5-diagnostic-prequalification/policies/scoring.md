# Scoring and Diagnostic Comparison — DRAFT / UNSEALED

Two independent blind scorers each receive all 15 reports for a mode in an
independent presentation order and decide every atom's direct criterion and
every closed defect rule. This is 16 scorer agents, not one scorer per report.
Two independent condition-blind consistency reviewers per mode each attest
every atom/defect family across A–O. This is 16 consistency agents. The
deterministic adjudication packet unions all scorer
disagreements, agreed-positive hard/global flags, consistency challenges, and
novel findings. At most one adjudicator per mode resolves all required cells.
Only then does the protocol merge direct results and propagate the atom DAG
into immediate `blocked_by`, derived `certificate_decision`, and transitive
`root_failures`.

These evaluator cohorts are launched only from committed predecessor stages:
Stage 01 derives scorer packets, Stage 02 consistency packets, Stage 03 the
conditional mode-adjudicator frontier, Stage 04 the shared materiality-review
packet and two reviewer launches, and Stage 05 the conditional
materiality-adjudicator packet. A successful run therefore has 154 through 163
sealed attempts and exactly six immutable aggregation stages. If any
evaluator's primary output is absent,
format-invalid, or semantic-invalid, the current phase still seals completely
but publishes an authenticated terminal `ERROR`; downstream scoring is not
filled in or guessed. Report bytes that are usable but over cap continue
through scoring and fail `D-OUTPUT-VALID` in the completed aggregate.

Hard errors and material findings are separate typed ledgers. Comparisons among
V5, V4, and no-skill are exact descriptive predicates fixed at integration;
five replicates do not license population, significance, or release claims.
The `D-*` gates describe diagnostic completeness only. The two failed `G-*`
environment gates keep `release_eligibility=false` regardless of scores.
