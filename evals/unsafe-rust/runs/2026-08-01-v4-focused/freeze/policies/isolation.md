# Frozen Isolation and Packet Policy

Each report cell receives a unique neutral runtime root with entries named only
`package`, `target`, `allowlist.txt`, and `output`. Inputs are copied
byte-for-byte, made read-only where the host permits, and verified against
frozen identities before launch and after the attempt. `output` begins empty.

The shared collaboration host does not provide a hardened per-agent mount or
network allowlist. Isolation therefore remains procedural. Runtime inputs must
not contain a repository, `.git`, evaluator files, mode/condition names, or
cross-cell paths. This limitation is disclosed in every result and prevents a
claim of cryptographically enforced blinding.

Before scorer launch, preserve and hash each canonical `report.md` and copy it
into a fresh mode packet under its frozen anonymous label. Chat-return text is
operational metadata and is not an alternative report channel. Prefer neutral
paths from collection so no report redaction is needed. Any required
normalization must use a frozen transformer and preserve the exact original,
transformed hash, and diff.

Scorer packets contain only the target, allowlist, common rules, one mode
rubric, ten anonymous reports, score schema, and packet-local hashes.
Consistency packets add only the two preserved raw scores and the consistency
schema for that same anonymous mode. All packet filesystem timestamps are
normalized to the Unix epoch. Packets contain no package, condition, run ID,
collection order, report-agent identity, or sibling mode. Adjudicator packets
contain only materialized review cells and their source evidence: scorer
disagreements, agreed-positive defect flags, consistency challenges, and novel
findings. They omit unrelated negative/agreed decisions.

The append-only event ledger externally pins the canonical collection index
and every complete scorer, consistency, and adjudicator packet byte tree.
Packet verification checks that external digest as well as the packet-local
manifest before every use. One run-wide operation lock serializes all state
checks, artifact writes, and event transitions. A canonical report, score,
consistency review, or adjudication and its attempt record derive from the same
single capture of the agent's output bytes; the protocol does not reread a live
output path to create either copy.

Failure preservation remains possible when an evaluated agent changes a
runtime input despite the procedural restrictions. The protocol binds the
expected neutral path, records expected and safely observed input identities
without following symlinks, and snapshots the entire neutral runtime on an
input or inventory verification failure. The snapshot preserves every regular
byte and records every directory, symlink, and special entry without following
symlinks. It also snapshots the central setup or source packet whose identity
was checked. Report input drift becomes a terminal scope failure; evaluator
packet drift makes the run `INVALID`. It never authorizes a retry.
