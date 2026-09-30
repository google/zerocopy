# Malformed consumer manifest: Lake preflight and server fallback

## Scope

This is one offline, package-local Lean/Lake 4.30.0-rc2 fixture for investigation **I092** in [#3731](https://github.com/google/zerocopy/issues/3731), with **F07** of [#3730](https://github.com/google/zerocopy/issues/3730) as historical context. It follows the [earlier resource-gated attempt](../anneal-3731-lake-malformed-manifest-preflight-refusal-2026-09-29/REPORT.md), which launched no Lake commands. This result establishes the behavior of the installed binaries identified by the hashes below; it does not establish behavior for other Lake versions, Anneal workspaces, or every malformed manifest.

The private producer defines `depValue : Nat := 7`; the consumer imports it, proves `depValue = 7` by `rfl`, and evaluates it. `lake build Generated` first seeded a valid producer `.olean` and a private artifact cache. In the valid phase, three consumer commands ran with `--no-build --no-cache` and network-disabled/private environment. The only change before the malformed phase was replacing the consumer `lake-manifest.json` with the exact two bytes `{@LF` (hex `7b 0a`). After the malformed commands and direct-Lean control, the original manifest bytes were restored and all three Lake commands repeated. Producer and cache inventory hashes stayed unchanged in each phase. The runner retained command arguments, environment overrides, PIDs, exits, raw stdout/stderr, protocol frames, inventories, and resource samples in [results.json](results.json), [raw/](raw/), and [work/](work/).

| Consumer manifest | `lake setup-file` | `lake env lean --json` | `lake serve` initialize/shutdown |
| --- | --- | --- | --- |
| Valid | exit 0; `Dep.olean` in `importArts` | exit 0; `#eval` reports `7` | responses to initialize and shutdown; exit 0; empty stderr |
| Malformed `{@LF` | exit 1; `invalid JSON: offset 2: unexpected end of input` | exit 1; same error | responses to initialize and shutdown; exit 0; stderr reports manifest error and fallback to plain `lean --server` |
| Exact valid bytes restored | same successful setup | same successful `7` | initialize/shutdown responses; exit 0; empty stderr |

`{@LF` in the table denotes the literal opening brace followed by line feed; [malformed-lake-manifest.json](fixtures/malformed-lake-manifest.json) retains the exact bytes. The valid manifest SHA-256 is `4cf0c1b12e990e08af5075710832c08e1df761220ab141edb2da7211cb2fd230`; malformed is `a6fb08fda1acb957b6116bd37811a1fe41a01611c0631edbf786d6889a27a55c`. The runner's `LEAN_PATH` is absent for every Lake command. A separate direct `lean --json Generated.lean` control explicitly pointed `LEAN_PATH` to the retained producer OLean directory, exited 0, and reported `7` while the consumer manifest was malformed.

## Interpretation and limit

For this fixture, Lake's `setup-file` and Lake-mediated batch invocation refused the malformed consumer manifest before reporting a usable setup or batch result. `lake serve` instead launched a protocol-speaking server through a documented-by-stderr fallback to plain `lean --server`; **a successful initialize handshake alone did not establish a valid Lake package setup**. The server transcript contains no `didOpen`, import check, goal request, or diagnostic comparison, so it does not establish whether that fallback could elaborate the consumer file. The direct Lean control shows that the retained producer OLean was independently usable with an explicit import path, not that Lake had recovered.

The initial acquisition is retained under [preliminary/](preliminary/) and excluded from these results because it supplied `LEAN_PATH` to Lake commands. The corrected acquisition used a fresh work directory and removed that confound. Its preflight measured 30.322% reclaimable RAM and 18,610,556,928 bytes free. Forty resource samples across 11 sequential processes showed at least 29.970% reclaimable RAM and 18,609,631,232 bytes free, at most 1,037,536 KiB summed process-group RSS and 235,464 bytes scratch. Every command finished within its 30-second timeout; no resource guard aborted. The evidence records parent-command exits, not a separate post-command child-process census.

Lake executable SHA-256: `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`. Lean executable SHA-256: `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. These executable hashes are the firm binary identities; this package does not independently attest the source commit from which they were built.

## Replay and verification

From this report directory, run `python3 -B check.py` for offline verification of the retained raw outputs, JSON-RPC frames, exact single-file corruption/restoration, inventories, command/environment controls, and resource limits. `probe.py` is the acquisition script; rerunning it is an active Lake/Lean experiment and requires the same resource admission. No network or dependency installation was used. The [fixture files](fixtures/) and final [private work tree](work/) are retained, with the valid manifest restored.
