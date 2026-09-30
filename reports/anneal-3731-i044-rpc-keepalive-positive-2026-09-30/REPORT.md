# Lean RPC keep-alive preserves one live rich reference past an observed idle-expiry interval

## Scope and result

One pinned Lean 4.30.0-rc2 `lean --server` session returned a real `InfoWithCtx` reference from `Lean.Widget.getInteractiveGoals`. `Lean.Widget.InteractiveDiagnostics.infoToInteractive` resolved that reference to `Nat` before and after a 43.1137-second interval. During the interval the client sent exactly five `$/lean/rpc/keepAlive` notifications, at 8.1408, 16.1996, 24.0836, 32.0991, and 40.1340 seconds, with the original URI and session ID. The same server and file-worker PIDs remained alive; the document was not edited, reopened, closed, or restarted. The final call reused the exact reference and session.

The published no-message control for the same source text, binary hash, harness hash, RPC method, and `{"p":"0"}` reference returned `-32900 Outdated RPC session` after 42.01 seconds. Together these two bounded runs show a positive keep-alive cell and a negative idle cell on this pin. They do not measure an exact timeout boundary or prove indefinite retention.

This adds direct component evidence to #3731 **I044** and context to #3730 **C08**. It does not establish Anneal's future reference or historical-query policy.

## Fixture and protocol

The file is an unfinished two-line theorem, `theorem hole (n : Nat) : n = n := by` followed by `  exact ?_`. It needs no imports, Lake package, plugin, or network. Its UTF-8 SHA-256 is `fdf822edf4b00ec43bd29cd96db47a87002fd5a761fa3922e2a34000e2943447`. A direct Lean server opened it as LSP document version 1, waited for diagnostics, connected an RPC session, requested interactive goals at line 1/character 8, and extracted the `info` reference on the `Nat` hypothesis type. The server then returned an interactive popup for that reference.

The retained event sequence has five client keep-alive messages and no other client message between the first successful dereference and the final request. Each notification had `params: {uri, sessionId}` and no request ID; the protocol supplies no acknowledgement. The decisive observation is the successful response to the later `infoToInteractive` request using the original reference. The final response again rendered `Nat`. Server-originated refresh requests were received after the final client request; the checker distinguishes these from client traffic and matches the response by request ID.

The locally available pinned `Lean/Data/Lsp/Extra.lean` documents a client-to-server `$/lean/rpc/keepAlive` notification at about ten-second intervals and expiry after three missed periods. Our 8-second schedule is a single concrete execution of that contract. The installed Lean executable SHA-256 is `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The source revision cited by the preceding idle-expiry report is a source-analysis pin; this package does not independently establish which source commit built the installed executable.

## Guard and retained evidence

At admission, estimated reclaimable RAM was 31.587% and free disk 18,655,956,992 bytes. Across 272 samples, minimum estimated reclaimable RAM was 30.5288%, peak server plus file-worker RSS 686,800,896 bytes, minimum free disk 18,651,951,104 bytes, and maximum scratch 48 bytes. The run stayed below its 1.2 GiB process-tree RSS and 100 MiB scratch limits and above its 20% live RAM and 10 GiB free-disk floors. The server exited 0, the post-stop process tree was empty, and the temporary source directory was removed.

`oracle.json` retained the fixture hash and intended schedule before launch. `results.json` retains the decoded ordered JSON-RPC events, request/response objects, process IDs, resource samples, and cleanup. These are harness-decoded events, not a separate capture of raw framed stdio bytes. `baseline-expiry-results.json` is the exact published no-message result (`4c7d2562d4b6203f9bc2a21b52a0af01d07a28f64ec6e266140d2bf3809e0257`). `check.py` verifies the retained event/result agreement, five notification payloads, exact reference/session reuse, no other client traffic within the interval, successful final response, baseline error, resource bounds, and cleanup. Run `python3 -B check.py` offline.

The probe reused the prior direct-server framing harness by its exact SHA-256 `9d5d5c7e3d85e8679e1ee04f9f8df485d163be3bd0eebaa0ffadaf27f7dc50a7`; `probe.py` stores that path and hash. It is a one-shot script whose result file prevents accidental rerun over the retained evidence. The initial no-message run and this keep-alive run occurred at different times, so host timing and resource conditions were not identical.

## Limits

Only one real rich reference, one session, one source version, one direct server, and one 43-second schedule were tested. There is no multi-reference retention curve, explicit-release negative control in this package, edit/import transition, crash, worker replacement, server restart, exact TTL measurement, or evidence that a reference remains valid forever. The prior direct Lean reports cover some release/replacement cases separately. No Anneal V2 server, editor, MCP broker, or generated proof workspace was exercised; any product-level reference lifetime and freshness rule remains to be implemented and tested.
