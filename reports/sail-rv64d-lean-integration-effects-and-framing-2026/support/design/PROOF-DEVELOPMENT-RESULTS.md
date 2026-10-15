# Bounded native proof development: accepted main theorem, controls unfinished

The six-check grant is exhausted. No further compiler check ran after check06. All checks used the exact granted existing container/official Lean4.29.0, -j1, -M4500, --tstack=400000,120s timeout; LEAN_PATH contained only completed serial-build-integration/olean plus the particular new owned proof directory. No model/support/import/tool/resource changes, other containers, installations, network, Git or publication occurred. No panic/assertion/invariant occurred. Native check duration sum is recorded in PROOF-DEVELOPMENT-RESULTS.json (about9.33 seconds), far below the10-minute native allocation.

## Accepted result

Check05 **exit0**,1.0645521740661934 seconds, child maximum RSS1555508KiB. Actual remote subject is `/home/opam/anneal-sail-output/proof-development/check-05/Proof.lean`, importing the unchanged full completed integration root and real interpreter. Exact copied local accepted source is `accepted-Proof.lean` (identical to Proof-v6.lean), SHA256 `f62057489d30152c39dcfab87c5b7ecbb43dd2e6bbe14d0368c4cbc832b6f2d4`. Accepted olean is `accepted-Proof.olean`,297080 bytes, SHA256 `a37ef2b0d8f2ed3613a85ae666e89771464e2453df0929f9f80fb44397faa3bf`.

Accepted theorems:

- AnnealSail.execute_add_effects: actual top-level execute RTYPE(Regidx2,Regidx1,Regidx3,ADD) equals exactly readx1→readx2→writex3(a+b)→Retire_Success(). Kernel proof is Eq.refl; there are no hidden choices/memory/system notifications in that specific free-effect tree.
- AnnealSail.execute_add_full_state: for all a,b:BitVec64 and all actual sequential states s, only x1/x2 presence assumptions, interpreted actual execute returns success and `{s with regs := s.regs.insert x3(a+b)}`. All unrelated fields, arbitrary/uninitialized register entries and memory remain as in s.
- AnnealSail.execute_add_register_frame: every generated register except x3 retains its dependent-map lookup, including missing entries.
- AnnealSail.execute_add_pc_frame: actual AST execution preserves PC lookup. No fetch/decode/PC+4/ABI/hardware/Rust-resource theorem is asserted.

The accepted source still contains its original historical header saying the source-derived draft was uncompiled; that comment is frozen in accepted source to preserve its checked byte identity. This result receipt supersedes that earlier status. No source claim or execution receipt is rewritten to hide failed attempts.

## Actual assumption audit

`native-check-05.stdout` preserves exact theorem statements/proof terms and all four individual #print axioms outputs. `accepted-proof-axioms.json` extracts each exact list. Each lists78 axioms and **none lists sorryAx**. They include platform/reservation/random/event/FP hooks and propext/Classical.choice/Quot.sound. This is not an axiom-free theorem or a source-external-free imported closure.

Lean CollectAxioms traverses the theorem's TYPE as well as proof value and whole referenced definitions syntactically. The real theorem type mentions actual whole Functions.execute; its syntactic closure therefore retains hooks from branches not selected by ADD. The exact rfl free-effect equality supports the narrower selected-path statement but does not remove that syntactic closure. Reporting these hooks honestly is required; no subject normalization, desired-result axiom or replacement executor was used to hide them.

## Preserved ordinary failures

Check01 (Proof-v2) failed ordinary elaboration: guessed LeanRV64D.instArch constant did not exist; frame lookup needed explicit Std.ExtDHashMap.get?_insert (not a simp-tagged lemma). Check02 (Proof-v3) fixed Arch via explicit inferInstance and closed frame, but the proposed nested-result change was not definitionally accepted. Check03 (Proof-v4) exposed generic monad/state projections; check04 (Proof-v5) reduced these to getThe. Check05 (Proof-v6) added getThe unfolding and passed. Every source version, exact argv, status, timing, complete separate stdout/stderr and hashes is preserved in host native-check-01..06 files and matching create-only remote check dirs. Original Proof.lean and parent's attempt1 remain unchanged. Warnings on some unused simp arguments are preserved; they do not change the accepted statement.

Check06 **exit1**,2.104641573037952 seconds, maxRSS1544292KiB. It used accepted check05 Proof.olean (hash verified in its receipt) to check Controls-v2.lean; no Controls.olean was produced. Ordinary failures:

- Missing-source interpreter reductions stopped at generic throwThe; add that projection to the existing unfolding list.
- fixture12/fixtureWrap's multi-line pipeline inside a record field parsed incorrectly; use explicitly nested insert applications.
- sub_fixture's split-line inserted value also violated record field layout; put the application on one line or explicitly parenthesize it.
- Remaining fixture goals and diagnostic sorryAx lists cascade from those failed declarations. They are **not accepted control proofs** and must never be cited as such.

Source-only `Controls-v3-uncompiled.lean` incorporates those concrete ordinary fixes while keeping the same assertions and full-root/Proof imports. It has **not been compiled** and is no success claim. Parent can review it for a separately authorized later check. No false-counterclaim rejection files or decoder theorem ran in this grant. The accepted universal arithmetic/frame theorem does not by itself fulfill the requested discriminatory control execution milestone.

## Reproduction and boundary

Parent can independently inspect native-check-05-result.json, compare accepted source/olean hashes to the raw remote files and review all four theorem types/axiom closures. Any independent replay must use the actual completed integration generated-model+support subject and official imported oleans, not original rejected or annotation-only subject artifacts. The parser/typechecking corrections did not alter theorem semantics or model source. Controls and final report/publication remain with the parent.
