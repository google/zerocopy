# Frozen Tool and Source Policy

Report agents may read only their per-cell package, target, URL-only allowlist,
allowed exact pages, and initially empty output directory. They may write only
`output/report.md` with `apply_patch`. Direct URL opens are permitted; web
search, link traversal, and every non-allowlisted page are prohibited.

Targets must not be modified, built, tested, executed, or macro-expanded by
execution. Report agents may not spawn helper agents. They must not inspect
sibling/enclosing paths, repository or Git data, evaluator material, schedules,
maps, other cells, or prior reports.

Scorers and adjudicators have analogous packet-only read scope and one-file
output scope. Tool and path restrictions are procedural on the shared host;
they are not a hardened sandbox. Every known deviation is preserved in the
append-only event ledger and fails the scope gate when material.
