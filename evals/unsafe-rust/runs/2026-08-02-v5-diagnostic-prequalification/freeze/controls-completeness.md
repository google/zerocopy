# V5 evaluator-control completeness

Status: **DRAFT / UNSEALED**. This note and `controls.json` are evaluator-only
materials and must not be included in report-agent inputs.

The control inventory has two deliberately separate families:

- `PROOF_QUALITY` groups the atom certificates that jointly establish a proof
  chain, reconstruction, authority reconciliation, dependency boundary, or
  other relationship whose quality cannot be measured from a conclusion alone.
- `CLASSIFICATION_CONTROL` identifies intended positive, fixed, downstream,
  reconstruction, and deliberately conditional control cases whose exact
  classification must remain stable.

Every one of the 115 atoms in the eight V5 atom manifests occurs in at least
one control. Every mode has at least one control in each family. Overlap between
families is intentional where a classification is also the endpoint of a proof
chain; it does not duplicate an atom certificate or change its weight.

The typed expected relation means that every listed atom's
`certificate_decision` must equal `PASS`. `PASS` describes correctness of the
report's atom certificate. It does not mean that the audited API or theorem is
sound: a correct `UNSOUND`, `UNPROVED`, rejection, or conditional conclusion can
and should receive a passing atom certificate.

`validate_controls.py` enforces exact manifest fields, stable ID/family/mode
agreement, fixture and applicability mappings, the typed relation, known and
same-mode atom references, both families in all modes, and exact total atom
coverage. Its set comparison rejects both orphan atoms and unknown references.
