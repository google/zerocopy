# Isolation Policy — DRAFT / UNSEALED

The intended evaluation boundary denies a report agent access to condition and
blind maps, sibling attempts, evaluator oracles, scores, alternate packages,
undeclared documentation, the network, and communication with other semantic
agents. V5 and V4 receive exactly one content-addressed package; `no_skill`
receives no package and an empty skill-instruction insertion.

The report templates contain one `{{INVOCATION_BLOCK}}` marker and no
agent-visible discussion of evaluation, conditions, skills, or mounts.
Integration renders that marker to the reviewed package invocation for V5/V4
and to zero bytes for no-skill. All other rendered prompt bytes for the same
target/regime must be identical across conditions; the ordinary no-skill
request therefore contains no hint that another treatment exists.

Each agent starts in a fresh opaque external workspace. Every rendered prompt
uses only the fixed workspace-relative aliases `input/` and `output/`, and the
materialized leaves are identical across conditions except that V5/V4 have one
package at `input/package/` while no-skill has no such entry. Absolute
workspace paths are coordinator-only fields in static-locked launch records;
they never occur in prompt bytes or agent-visible input documents.

This collaboration environment does not enforce that boundary: agents share a
checkout and coordinator/tool mediation. The executable manifest therefore
fixes `G-ISOLATION` to direct `FAIL`. Procedural restraint is useful for
diagnostics but cannot change release eligibility.
