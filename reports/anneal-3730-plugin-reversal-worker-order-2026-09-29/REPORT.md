# Native plugin reversal across Lean file workers and restart

## Result

One pinned Lean 4.30.0-rc2 watchdog opened three proof files while the same native plugin path was atomically changed from valid v1 to valid v2 and back to v1. Each newly opened file produced the matching initializer marker: `plugin-v1`, `plugin-v2`, `plugin-v1`. Previously opened proof files still answered `no goals` after each replacement. After that watchdog exited, a fresh server opened a fourth file and again produced `plugin-v1`. All four diagnostics waits and proof goal requests succeeded; both servers exited 0.

This adds a reverse-order and restart contamination sentinel for I125/I154. The prior native-plugin report already established v1→v2 replacement, an old file worker remaining usable, a newly opened worker loading v2, a fresh v2 server, and a wrong-initializer failure. The new result checks v1→v2→v1 in one watchdog and the final fresh worker. It does not establish a general native ABI compatibility rule or a product-wide plugin identity policy.

## Subject and controls

The fixture copied the prior report's prepared v1 tree into this package's private `support/work/live`. `Dep.olean` and proof bytes stayed fixed. `support/artifacts/` retains the exact v1 and v2 dylibs; their SHA-256s, the pinned Lean binary SHA-256, the imported OLean SHA-256, every LSP frame, marker observation, and event order are in `support/transcript.json`. The plugin initializer writes the compiled-in tag to `PLUGIN_MARKER`; a marker is an execution witness for a new file worker, not an internal attestation from Lean's loader. The old proof result remains a usability witness only.

The host memory preflight required at least 20% reported free memory and disk preflight more than 2 GiB. Only one Lean server ran at a time. Replacements used a copied file followed by `os.replace` at the stable plugin path. The retained server shut down before the fresh server started. No package install, download, published report edit, or shared toolchain mutation occurred.

| Event | Plugin path SHA | New file marker | Goal |
| --- | --- | --- | --- |
| First file in retained server | v1 | `plugin-v1` | no goals |
| New file after v1→v2 | v2 | `plugin-v2` | no goals |
| New file after v2→v1 | v1 | `plugin-v1` | no goals |
| New server, fourth file | v1 | `plugin-v1` | no goals |

The exact hashes are in the transcript and checked against retained dylib bytes. The final file and OLean hashes equal their initial identities. Search-path collisions, an actual plugin-defined proposition change, multiple plugin dependencies, process mapping inspection, and Anneal worker routing remain unresolved.

## Recheck

Run `python3 support/check.py` to validate saved bytes, marker order, wire responses and sequential server lifetimes offline. `python3 support/probe.py` re-executes using the pinned local Lean binary and the retained prior report's v1 tree; it rewrites only this package's `support/work` and transcript. A changed binary or fixture is a new subject.
