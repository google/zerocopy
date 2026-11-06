# Public evidence representation

*Authored by an AI agent acting on joshlf's behalf.*

This package preserves the actual pilot source, assembly, fixed vectors/oracles,
zerocopy source selection, object/final ELF bytes, LLVM IR, disassembly and target
stdout/stderr unchanged. The four original ELF identities in REPORT.md identify
the executed images. Host copies remain nonexecutable data.

Some support metadata, host diagnostic streams and two historical static-helper
copies replace the local workspace, host Docker CLI and Docker socket prefixes
with `/path/to/anneal-workspace`, `/path/to/docker` and `/path/to/docker.sock`.
These are display substitutions, not executed argv or rerun helpers. The complete
changed-file counts, raw/display hashes and prefix digests/lengths are recorded
in public-projection.json. Original local prefix strings are deliberately omitted.
The parent compared each transformation with the retained original; the independent
review must bind its verdict to this exact public candidate.

RESULTS-FREEZE.json and the compile/runtime preparation manifests retain original
raw file identities. For projected files those historical hashes are not hashes
of their public display copies. package-manifest.json records the complete public
package, apart from itself. REPORT.md's small editorial change explains this
representation; no observed value, status, target/tool/image hash, compiler flag,
source-domain restriction or proof claim changes.

No public helper copy was executed after projection. Repeating the experiment
requires fresh path/tool bindings, a new output namespace and a new review of the
capture program. Existing accepted checks concern the original fixed experiment;
the public path placeholders do not authorize a different subject or environment.
