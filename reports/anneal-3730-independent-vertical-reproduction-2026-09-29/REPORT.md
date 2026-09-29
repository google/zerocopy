# Procedural reproduction of the Lean vertical acceptance prototype

## Summary

A second GPT-6 Sol High worker wrote a separate driver for the preserved vertical report's small Rust-comment → generated-Lean → live-goal → fresh-check procedure and ran it twice in new isolated temporary directories. The A and B source/model/proof hashes, their compiled model/proof artifact hashes, fresh fixed-consumer results, invalid F model exit, stale A proof failure under B, and final B selection agreed with the original. The live server showed A's unfinished `⊢ modelValue = 3`, then `no goals` after an unsaved edit; B showed `no goals`; the old A proof under B showed `⊢ modelValue = 3`. An old A build was paused before F failure and B publication, completed afterward, and was rejected by the new driver's revision fence. The comparison script found **33/33 expected-exact fields equal**, plus four intentional source-layout differences.

This is an independent **driver and fresh process run** on the **same host and Lean binary**, not an independent Lean implementation, human study, or Anneal reproduction. The author had previously read parts of the original `run.py` while preparing another report, so it is **not a blind reconstruction**. The original raw transcript was consulted only after the new runs to compare outcomes. No real Anneal, Charon, Aeneas, or Lake pipeline was executed.

## Applicability

The executable was Lean `v4.30.0-rc2`, commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, binary SHA-256 `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`, run on macOS arm64 with `LEAN_NUM_THREADS=1`. The new Python 3.14.7 standard-library driver writes a fresh temporary fixture under the conversation-owned Meta/Data scratch directory for each run, using only `LEAN_BIN` and `ANNEAL_PROBE_SCRATCH` as required input. It deletes its temporary workspace after serializing source/artifact hashes, complete normalized compiler JSON, LSP messages, gate events, and publication decisions. It never executes or edits the original package's `support/run.py` or retained `support/work/` tree.

The fixture is intentionally the original's narrow manual translation: parse `pub const MODEL_VALUE: u8 = N;`, generate `def modelValue : Nat := N`, and project `// anneal:` lines into `Proof.lean`. The A, B and invalid F text was reconstructed from the report's described procedure and known small fixture shape. This contains no real Rust parsing or translation. The original package's `REPORT.md` and third transcript were fixed comparison subjects; `support/compare.py` reads them without modifying them.

## Findings

### Same input and compiler yielded exact A/B artifacts

The new driver rebuilt A (`modelValue = 3`) and B (`modelValue = 4`) in separate directories. A's initial unfinished annotation remained on disk while the direct server opened that text as version 1, reported `⊢ modelValue = 3`, received the completed `rfl` proof as version 2, and reported `no goals`. A's exact version-2 proof was then checked by a new `lean --json` process, compiled as `Proof.olean` by another, and consumed by a third process checking `example : modelValue = 3 := claim` plus `#print axioms claim`. B followed the same direct-server and fresh-process pattern for `modelValue = 4`. Both consumers exited 0 and reported no axioms in both new runs. Basis: **execution**; the accepted meaning is restricted to these fixed Lean propositions.

All A-initial, A, B and F host/model/proof *source* hashes matched the original retained transcript. A and B compiled `Generated.olean` hashes matched exactly: `9dd4d2a1c8cf7d909299d4bb92a45f8ff3f7c4593f8913b64eafa1eed800b4e5` and `9ed8713387b59eaf45c0f261cb92ed8ad4663c86301973e57e73f1441a38`. A and B compiled `Proof.olean` hashes also matched exactly: `24ff1eadf3b0456611ff00202c150f89980e801b5832d65fcf12f14bb39519e0` and `ba08ca066322195e2b2271b4c4eae8249a84eabdb18ea912ba210d98da8ff41b`. These are observed byte equalities for the same tiny input/toolchain, not a promise of cross-path or cross-version `.olean` reproducibility. The new script also recorded equal A/B fixed-oracle source hashes and exits. Basis: **execution** plus exact transcript comparison.

### Failure, stale proof and late output retained their own identities

After selecting A at prototype revision 1, the new driver started an A proof compiler and waited until its Lean `run_tac` wrote `gate.entered`. It then advanced host authority to F at revision 2. The intentionally invalid `Generated.lean` failed with `unexpected end of input`, leaving A as last-known-good only. The driver advanced to B at revision 3, rebuilt B, checked its theorem and selected B. Only then did it release the old A gate. That process exited 0 and its old fixed consumer exited 0, but the driver rejected it because candidate revision 1 was older than selected revision 3. A compare-and-swap edit carrying A's old source hash was also rejected after B became authoritative. This is a real causal order for the child compiler and a **prototype** fence decision; it does not validate Anneal's publisher.

An A `rfl` proof copied into B's imported model exited 1 in fresh batch Lean and reported `⊢ modelValue = 3` under the direct B server. A weakened `claim : True` proof compiled yet failed B's expected-proposition consumer. A `sorry` proof compiled and passed that consumer, while `#print axioms claim` reported `sorryAx`. The two new runs reproduced these classifications. The fixed-consumer and axiom checks are independent *process invocations* of the same Lean binary, not an independent checker or full Rust obligation audit. Basis: **execution**.

### Exact comparison and divergences

`support/compare.py` evaluates the second new run against the original third transcript. Its 33 expected-exact fields include A-initial/A/B/F host/model/proof hashes, A/B model/proof artifact hashes and checker exits, oracle hashes, failed F exit, stale batch/live outcome, late selection and final B pointer. It also verifies the causal order in each transcript: old gate entered → F failure → B selected → old A completed → stale decision. All 33 comparisons and both order assertions passed. This is a direct **comparison**, not 33 independent scientific replications; many fields share source and compiler causes.

Four source-layout differences are expected and preserved in `support/comparison.json`:

| Case | Original | New driver | Consequence |
| --- | --- | --- | --- |
| Weak B proof source | `e9de96e0…c506e9` | `f72a7e7c…f8d8` | Different tactic whitespace/layout; same proof-exit 0 and consumer-exit 1. |
| Admitted B proof source | `96b39d63…bb6b84b98f` | `56678542…f19878b1` | Different tactic whitespace/layout; same proof/consumer exits 0 and `sorryAx`. |
| Late A generated source | `fc40104c…22c485` | `de1854df…5037a91` | Original placed the gate in a generated module; new driver keeps A's model unchanged. |
| Late A proof source | `a1278057…c45956` | `aaa2040b…c12ac7678` | New driver places the gate in the old proof, so its late proof artifact bytes are not expected to match. |

Moving the gate changes the exact late candidate and means this reproduction supports the **causal stale-publication classification**, not byte identity for the original A-late artifact. Weak/admitted cases reproduce the intended comparator behavior, not the original proof bytes. No unexpected semantic divergence was observed in the two new runs. The new runs' varying PIDs, timing, and temporary paths are deliberately excluded from exact comparison.

## Boundaries

- The author is another agent worker, but used the same host, file system, Lean binary, and issue context; prior exposure to the original `run.py` prevents a blind-reconstruction claim. The fresh scripts and temporary workspaces are independent of the original script's execution state.
- Both drivers share the manually specified translation rule and fixed Lean propositions. Neither checks real Charon/Aeneas output, actual Anneal annotation syntax, Rust-level obligation coverage, imported artifact provenance beyond the recorded hash, or an independent proof kernel.
- The in-memory selected pointer, compare-and-swap authority, and revision fence are new prototype Python decisions. Their matching classifications do not show an implemented Anneal scheduler or crash-safe publication.
- The gate placement intentionally differs for A-late; the two late candidates are semantically old-A examples but do not have identical source/compiled artifact bytes. The weak and admitted control sources also differ in layout.
- This was one operator role with two repeated runs, not an independent machine/operator, cross-version matrix, blinded evaluation, or human trial. It partially addresses I136's procedural reproduction cell; the independent-environment/operator and upgrade cells remain.

## Evidence

- Independent driver `support/reproduce.py`, SHA-256 `80ba94089321454a35443a8d469870d4820ebb952f4a019f3a1d0609c99a29fa`, contains complete fixture construction, JSON-RPC client, process gate, controlled publication, negative controls, and assertions. `support/reproduction-run1.json` and `support/reproduction-run2.json`, SHA-256 `4fb59f5002108823774acda77288593b6c603406cf1a7e3ae0af1d376541e6c0` and `0b8f70e8cd6d15194a338917e75e6b9c838b4b733bb214f517fff3ddb3534991`, retain normalized raw commands/messages and classifications. Basis: **execution**.
- Comparison script `support/compare.py`, SHA-256 `8087416a9167908f18c79d8e9872a5d300f3506960f7fdf33380ce7bd58227e5`, and `support/comparison.json`, SHA-256 `9da6b7f2704df27ff566eccf737ce1fd20c6e7f8805f78ed4a35d8766cf679ad`, retain each exact field, expected-divergent source hash and causal-order check. The original [`vertical report`](../anneal-3730-vertical-acceptance-v4-30-0-rc2/REPORT.md), SHA-256 `8ec34505ae7c3bad9f9840788a6d17ddf60293e2b5060f54e033336833acf409`, and original `support/transcript-run3.json`, SHA-256 `55e0dfc1083ee7d1a5ee5f71f9517a0018f2d4db81148a2843da4d97fd03bf80`, are comparison inputs. Basis: **execution** and **derived comparison**.
- The new driver did not read original raw outcomes at runtime. The original raw transcript was opened after both initial new runs, and the comparison was then automated and rerun after adding the live stale-proof control. The added control and its limitations are visible in the script and report. No original package file was changed.

## Revalidation

With the pinned Lean binary, run `LEAN_BIN=/absolute/path/to/lean ANNEAL_PROBE_SCRATCH=/owned/scratch python3 support/reproduce.py` from this package; it writes `support/results.json`. Verify A initial/edited and B/stale live goals, A/B three fresh-process checks, F parser failure, old-gated A completion after B publication, stale pointer rejection, and weak/admitted comparator outcomes. The script creates a new temporary directory each time. To compare with the preserved original third transcript, move or copy the resulting JSON to `support/reproduction-run2.json` and run `python3 support/compare.py`; it asserts the 33 exact fields and both causal orderings. For a stronger I136 replication, use a separate operator/environment and a deliberately selected compatible Lean upgrade, retaining new immutable tool and input identities.
