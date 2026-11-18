# Research binding: reference/1

Use this resource only when the caller selects `reference/1`. Read the complete
bound native policy and format; they own meanings and commands. This resource
preserves the package-specific obligations used by the shared research process.

The binding selects `AGENTS.md`, `FORMAT.md`, `CATALOG.json`, the candidate-local
`tools/reference.py` and the complete research materialization. Check existing
coverage by querying the catalog programmatically by package, `topics` or
`subjects` with Python or `jq`, then read relevant `reports/<package>/` originals.
Package names and retrieval labels do not establish technical applicability.

Coalesce reports under `reports/<package>/`, with `REPORT.json`, `REPORT.md` and
optional `support/`. Use native canonical top-level `topics` and the six required
H2 sections: Summary, Applicability, Findings, Boundaries, Evidence and Revalidation.
Carry the native evidence roles `normative`, `documentation`, `source`, `execution`
and `derived` into investigation briefs and distinguish their support in reports.
Record unresolved/out-of-scope work in Boundaries as unknown or not examined.

When extending an existing topic, prefer coalescing covered versions into that
package. Put durable upstream revisions or release identities in `REPORT.json`
subjects; never use a corpus commit, local worktree or throwaway experiment as an
upstream subject. Explain shared/different behaviors in Applicability and Findings.
Retain standalone probes and reproducible definitions in `support/`.

Keep research scratch outside the candidate. Only final packages and regenerated
native catalog belong there. Parallel authors receive disjoint package paths;
the coordinator alone regenerates shared state and validates the whole candidate:

```console
python3 tools/reference.py catalog
python3 tools/reference.py check
```

These are the native standalone tool's commands, not universal corpus commands.
They check machine-representable invariants; semantic report quality still needs
review. Perform publication only with current action authority and the native
base/concurrency/readback procedure. Navigator installation remains optional.
