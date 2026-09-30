# Stepwise direct Lean document-version observations

## Result

One pinned Lean 4.30.0-rc2 direct server received full-text `didChange` notifications in the order **v2, v4, duplicate v4 with different bytes, lower v3, v5**, after opening v1. The client awaited `textDocument/waitForDiagnostics` at each step, observed a unique marker-bearing `publishDiagnostics` notification, then queried `$/lean/plainGoal` before sending the next change. The successive goals were **`1=1`, `2=2`, `4=4`, `40=40`, `3=3`, `5=5`**. A second v5 goal after a 1.5-second quiet interval remained `5=5`. A separate, sequential fresh server given strictly increasing versions v1→v2→v3→v4→v5 returned the corresponding `1`, `2`, `3`, `4`, `5` goals and also remained at v5 after its quiet interval.

The duplicate and lower-version inputs deliberately violate the monotonic document-version assumption in the installed Lean server source. Their observed content was accepted and exposed in this direct run; this is **not** a protocol-compliance verdict, a real lost-message test, or an Anneal reconciliation result. It adds a bounded intermediate-state cell to #3731 **I112**, whose prior direct Lean edit-storm report sent a 2/4/4/3/5 burst but measured only the final v5 state. The #3730 crosswalk has no direct suggestion link to I112, so this report does not update a #3730 row.

## Fixture and procedure

Each version is a small theorem with an intentionally unresolved `exact ?_`, plus a unique `#check missing_*` line. The theorem goal numeral is unique to the content: v1→1, v2→2, first v4→4, duplicate v4→40, late v3→3, and v5→5. `oracle.json` retains every exact source string and SHA-256, sequence, cursor position, tool hashes and guard thresholds. `Proof-v1.lean` has SHA-256 `976f64febc49d1f8a3c8ea7125f3d2f2ccc8f932457b75842b7d70c3506a0209`. Disk `Proof.lean` remained those v1 bytes during each server run; all later versions were unsaved full-text notifications. The two servers had separate private roots and ran one at a time.

For each notification, the retained ordered events show the exact source and version, the diagnostics wait request/response, at least one diagnostic containing that source's unique `missing_*` marker and the same announced version, and the plain-goal request/response. Each marker publication occurred before its goal request. This ties each observed goal to a source that the server had processed before the next notification. `waitForDiagnostics` by itself is not a strict identity proof for a repeated/lower version; the unique diagnostic marker supplies the discriminating observation in this fixture. The goal request has no version parameter, so the result is the content exposed at that moment, not a version-addressed historical query.

After both servers exited, six fresh `lean --json` batch processes checked the exact variant bytes at separate filenames. All exited 1 as expected from the intentional placeholder and unknown `missing_*` identifier. Every batch output contained its variant's marker and corresponding `⊢ n = n` text. These controls confirm that the source variants were distinct and generated the expected diagnostic/goal text in a fresh process; they are not successful proof-verification controls or the same module identity as the live URI.

## Observations and resource guard

| Stage | Sent version | Content marker | Live goal after marker |
| --- | ---: | --- | --- |
| Open | 1 | `missing_v1` | `⊢ 1 = 1` |
| Change | 2 | `missing_v2` | `⊢ 2 = 2` |
| Skip to | 4 | `missing_v4` | `⊢ 4 = 4` |
| Duplicate | 4 | `missing_v4dup` | `⊢ 40 = 40` |
| Lower than current | 3 | `missing_v3` | `⊢ 3 = 3` |
| Final | 5 | `missing_v5` | `⊢ 5 = 5` |

The separate monotonic control produced matching source-specific goals for v1, v2, v3, v4 and v5. Both server processes exited 0 and their post-stop process trees were empty. The malformed sequence's server ran for 4.9769 seconds; the monotonic one for 3.2866 seconds. Six batch controls each completed in under 0.17 seconds.

Fresh initial admission measured **31.9651%** estimated reclaimable RAM and **18,547,433,472** free disk bytes. Across 53 samples, minimum reclaimable estimate was **30.6545%**, minimum disk **18,546,282,496** bytes, peak summed process-tree RSS **689,438,720** bytes, and peak owned scratch **469** bytes. Each server was under its 30-second limit; live floors were 20% RAM and 10 GiB disk, ceilings 1.2 GiB RSS and 100 MiB scratch. These are samples, not unsampled peaks or unique physical memory. The temporary work directory was removed.

The installed Lean executable SHA-256 is `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The direct-server framing harness was reused by SHA-256 `9d5d5c7e3d85e8679e1ee04f9f8df485d163be3bd0eebaa0ffadaf27f7dc50a7`. The installed `Lean/Server/FileWorker.lean` source comments that version updates are assumed monotonous; this package does not independently establish the commit that built the binary. The executable hash and the retained execution are the firm identity/evidence.

## Evidence and limits

`results.json` retains 169 harness-decoded ordered JSON-RPC/lifecycle events, both server step grids, the two quiet queries, six complete batch stdout/stderr records and 53 resource samples. It is not a separate raw framed stdio capture. `check.py` independently maps exact wire messages, request IDs, source hashes, versioned marker publications before goal calls, goal text, disk-v1 state, fresh batch outputs, resource bounds and clean process exits to the retained result. Run `python3 -B check.py` offline; it does not launch Lean. `probe.py` is a guarded one-shot reproduction script that refuses to overwrite its own work/results paths.

This one ordered stdio experiment injected nonmonotonic versions; it did not drop an OS filesystem event, watcher notification, LSP frame or MCP message, nor disconnect/reconnect a client. A second goal after 1.5 seconds does not establish long-term quiescence. No editor authority, Anneal source snapshot, broker, durable event stream or reconciliation protocol ran. I112 therefore remains partial at its product gate. A product test must define how an authoritative source/version is restored after actual delivery loss and reject stale query publication across worker generations.
