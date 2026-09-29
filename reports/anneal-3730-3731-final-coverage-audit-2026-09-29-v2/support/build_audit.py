#!/usr/bin/env python3
"""Rebuild the 09:12+ UTC issue #3730/#3731 coverage snapshot.

The new package-to-item mapping and residuals were curated by reading actual
report methods, results, and boundaries.  This is an evidence audit, not a
re-execution of every upstream experiment or an implementation certification.
"""
from __future__ import annotations

import csv
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPORTS = HERE.parents[1]
PRIOR = REPORTS / "anneal-3730-3731-final-coverage-audit-2026-09-29" / "support"
sys.path.insert(0, str(REPORTS.parent / "tools"))
import reference


# IDs are specific methods touched by the report, not title-keyword matches.
P = {
    "anneal-3730-annotation-subject-boundary-matrix-2026-09-29": (
        [17,18,19,20,21,22,23,24,28,35],
        "Real rustc/Cargo/Charon/Lean on one invented comment-marker crate: malformed Rust, multi-annotation/helper, default/feature/test subjects, moved/duplicated item, proof-comment read by include_str/build.rs.",
        "Marker locator/projector is illustrative; no actual Anneal parser, last-good proof session, streamed batch/live generator or adoption choice."),
    "anneal-3730-charon-concurrency-interruption-2026-09-29": (
        [73,76,77,78,79,80,105,148],
        "Pinned Charon direct/Cargo two-process separate and shared destination trials, malformed shared JSON witnesses, controlled --format all FIFO stop after JSON, retry and stale-output failure.",
        "At most two tiny crates; kill boundary is before regular Postcard artifact, not all extraction phases or an Anneal output transaction."),
    "anneal-3730-charon-warm-target-controls-2026-09-29": (
        [73,74,75,76,77,78,79,80],
        "Pinned Charon/Cargo warm target sentinel and absent-output controls; copied B shadow/private/shared-target path-sensitive build script produced 217/205 mixed subject; failed warm run retained old LLBC.",
        "One selected --package --lib wrapper and path-sensitive fixture; no unsaved editor overlay, general target closure or same-process Charon reset."),
    "anneal-3730-identity-state-mutation-model-2026-09-29": (
        [11,13,14,16,18,20,21,34,45,145,147],
        "Finite 2,710-state/11,060-transition identity model and six two-writer schedules; A-B-A, version reset, alias, worker/RPC replacement and source/artifact decoupling; four forced Python writer runs.",
        "Symbolic and Python model only; no Anneal, Cargo, Lean, filesystem watcher or actual MCP client."),
    "anneal-3730-lake-plugin-artifact-identity-v4-30-0-rc2": (
        [50,98,120,125,150],
        "Pinned Lean/Lake direct batch/no-build and live plugin fixture: missing OLean/ILean/C/dylib by operation, dylib v1/v2 replacement, existing/new worker split and initializer mismatch crash.",
        "Tiny explicit plugin; no general ABI equivalence, all search paths, generated Anneal archive or complete interactive operation inventory."),
    "anneal-3730-lake-writer-recovery-2026-09-29": (
        [92,98,102,108,109,151],
        "Real Lake artifact-cache writer killed during paused Dep elaboration, two consumers with one killed writer, repaired no-build/ordinary build, truncated output-map rejection and retry.",
        "Kill precedes cache publication; no crash at mapping rename or same-package concurrent writer proof."),
    "anneal-3730-lean-cross-version-equivalence-v4-29-v4-30-rc2-2026-09-29": (
        [94,99,100,131,132,135,136,147,158,159],
        "Cached Lean 4.29 and 4.30-rc2 tiny clean/prepared direct/Lake batch and three live launch modes; source-only and valid OLean-only mutation, theorem/axiom/goal diagnostics and file hashes.",
        "Within-version small fixture only; batch/live select different artifact generations after mutations; not a compatible newer release or cross-version binary migration."),
    "anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2": (
        [41,42,43,44,45,46,47,48,49,50,91,147,159],
        "Direct/Lake-env/lake-serve same imported-definition matrix: source-only and OLean-only mutations, watcher, existing/new/reopened/fresh worker, batch, six goal positions and unsaved missing-header setup-file controls.",
        "One direct-import fixture inside Lake workspace; no transitive/option/plugin graph, exact import digest response, rich RPC or real Anneal server."),
    "anneal-3730-projection-macro-doccomment-patch-matrix-2026-09-29": (
        [25,26,27,28,29,30,31,32],
        "Pinned rustc/Charon macro span and Lean diagnostic specimens plus invented doc-comment projector: one-to-many/many-to-one maps, atomic two-range patch with nine rejects and 80-step indexed/full comparison.",
        "Invented ///| syntax and projector, not Anneal or a real LSP client; no materialized-versus-streamed generator comparison."),
    "anneal-3730-real-lean-filesystem-lifetimes-2026-09-29": (
        [123,124],
        "Real value-7/value-9 Lean OLean and plugin artifact bytes under host APFS aliases, replacement/unlink, resident/fresh Lean and open fd/mmap; cached Linux overlayfs byte lifetime replay.",
        "Linux container has no Lean; no native ext4/XFS/Windows/network filesystem or Anneal identity routing and GC."),
    "anneal-3730-upstream-api-projection-precedents-2026-09-29": (
        [2,3,8],
        "Pinned Lean and rust-analyzer source/API, Volar SourceMap and completion/WorkspaceEdit paths; dependency-free model of ambiguous, cross-segment and dropped auxiliary edits.",
        "No real Volar/Razor/Anneal process or upstream patch/adapter comparison; source interpretation and adversarial model are distinct from runtime behavior."),
}

# Only rows whose previous residual became materially stale need replacement.
DELTA = {
 2:"Run an actual editor-versus-fresh-compiler comparison over matched source and imported artifacts; pinned Lean/rust-analyzer APIs and earlier TypeScript/Roslyn/clangd precedent analysis do not prove parity.",
 3:"Execute a real Volar/Razor-style embedded-language client with virtual URI, ambiguous map, completion/code-action edits and two language services; pinned Volar source plus the adversarial Python model are narrower.",
 8:"Implement the conservative adapter in Anneal and compare its exact-version/import/projection behavior and cost with a minimal upstream API patch under the same acceptance oracle; pinned call sites only identify candidates.",
 11:"Test the modeled ABA/version-reset/alias counterexamples through an actual Anneal handle and worker lifecycle, including request-ID reuse and disk reconstruction.",
 13:"Perform a coherent two-document proof/helper update while real queries run; finite two-writer CAS schedules have no actual generated-document boundary.",
 14:"Run four independent actual writers on one Anneal workspace with conflict/fork/owner policy; finite and two-thread models expose the lost-update contract only.",
 16:"Reconstruct a real Anneal workspace after restart from disk plus unsaved reconnecting editor buffers; the finite model has no process state.",
 17:"Run the actual Anneal annotation grammar/parser through unfinished Rust and Lean; the invented marker locator survives malformed Rust but has no compiler-backed subject then.",
 18:"Build a real proof-only classifier and challenge its Cargo closure; the comment-read include/build-script counterexample defeats a broad text-only skip but does not classify all edits.",
 19:"Attach actual Anneal annotations to compiler items across cfg, aliases, trait defaults, locals and generated items; the line-marker ambiguity and Charon spans are not an attachment implementation.",
 20:"Select and label a complete compilation subject for the same source across lib/test/bin/features/targets, then test wrong-subject model/proof rejection; this fixture covered default/feature/test only.",
 21:"Maintain real annotation identity across move, duplicate, split, reorder and delete while queries are pending; the marker locator and finite alias model give selected counterexamples.",
 22:"Test actual parser/scaffolding visibility and collisions for multiple annotations, shared helpers, imports and recursion; the invented five-marker helper fixture covers only a slice.",
 23:"Continue a real proof against an explicitly named last-good model through Rust syntax, extraction and signature failures, and evaluate whether humans/agents understand its provisional age; malformed-Rust discovery alone is insufficient.",
 24:"Preserve real unsaved authored proof text through Anneal regeneration, formatter, duplicate/move and external edit; comment-marker source preservation is an illustrative control.",
 25:"Run negotiated LSP byte/UTF-16/scalar conversions through an actual Rust host and Anneal projection; macro and doc-comment fixtures remain model mappings.",
 26:"Exercise actual annotation stripping/escaping/scaffolding map inversion and cross-segment edit refusal; invented doc-comment rules cannot establish Anneal's map.",
 27:"Route actual one-to-many obligations/many-to-one declarations, diagnostics and edits to authored Rust; the new projector's duplicate map is illustrative.",
 28:"Materialize and stream one real generator through separate batch/live sinks and compare text, module context, maps and declarations under incomplete proofs and import edits; the new projector has one output path.",
 29:"Apply real projected patches after unrelated source shifts and conflicting writers with source-plus-projection CAS; the model rejects nine cases but has no editor/server transport.",
 30:"Exercise actual Lean completion and code actions, including snippets, imports, multi-edit atomicity and generated-only spans, through the Rust-hosted projection; the new model edits are hand-authored.",
 31:"Compare real Lean diagnostic provenance across authored, scaffold, generated model and imports, with ambiguous/missing span policy; the pinned diagnostics were only routed by an invented map.",
 32:"Fuzz the actual annotation grammar/edit stream and measure full versus incremental maps at useful size; this tiny invented projector's indexed path was slower over 80 steps.",
 34:"Compare stable URI and generation-path behavior with a real worker across regeneration/reopen; the finite response model has no document routing.",
 41:"Add causally gated version/query races during worker replacement and a real client fence; the three-mode import matrix demonstrates stale environment but no complete exact-version protocol.",
 42:"Separate parse/import/elaboration/async readiness with causal barriers and current-position status; missing-import wait success adds a failure control only.",
 43:"Extend direct Lean positions to nested tactics, combinators, macros and rich RPC; the new report sampled six plainGoal columns in one proof.",
 44:"Dereference/release/expire rich RPC objects across import replacement; the launch report used plainGoal and adds no RPC handle-lifetime result.",
 45:"Delay a successful old response through actual internal worker replacement, including reused request IDs on one transport; reopening/fresh-worker controls are narrower.",
 47:"Measure retained historical-goal storage, latency and expiry after rapid edits; a resident old worker is not an explicit historical-query service.",
 48:"Obtain or reconstruct exact loaded OLean/options/plugin/source and worker identity for a real project; setup-file paths and value sentinels are not an attestation API.",
 49:"No residual for the requested three-mode direct Lean imported-definition counterexample at v4.30.0-rc2: watcher, old/new/reopened/fresh workers and fresh batch were compared. Wider graphs and product use remain I050/I048/I157.",
 50:"Exercise transitive import, package option, macro and native-plugin mutation across old/new workers in the same launch matrix; the plugin-replacement fixture is one separate cell.",
 73:"Compare a real unsaved Rust editor overlay with saved extraction on identical intended bytes and label which source version was checked; the copied B materialization did not use an overlay API.",
 74:"Extend copied workspace path-sensitivity to proc macros, env/target inputs, generated files and general shadow-construction closure; the shared warmed target reused a stale path-sensitive generated constant.",
 75:"Test other wrappers/target kinds and selected Cargo/Charon revisions with successful-request echo; under tested --package --lib flags, warm target did regenerate LLBC despite ordinary Cargo Fresh.",
 76:"Add host/target/feature/same-name compilation units and destination arbitration; the two-crate concurrent output collision witnesses are real but narrow.",
 77:"Test same-process Charon reset after error/cancellation and compare fresh oracle; separate process A/B/A and output collisions do not establish reusable-library safety.",
 78:"Implement request-private multi-artifact publication and manifest validation around real Charon, including kills at all regular-file output phases; shared JSON corruption and FIFO stop show need only.",
 79:"Calibrate semantic LLBC normalization across source reordering, metadata/flags/path and compiler revisions while retaining provenance; the new runs compare selected byte/body cases.",
 80:"Measure resource sharing, child cleanup and contention for parallel snapshots across more target kinds; new runs had at most two tiny Charon processes and one target-reuse hazard.",
 91:"Instrument actual server setup-file headers/options/plugins for unsaved imports; explicit command override works but the server's hidden invocation was not captured.",
 92:"Probe server no-build behavior for all incomplete artifact/config families in a prepared real generated consumer; new Lake/plugin/cache runs cover selected operations.",
 98:"Mix valid but incompatible OLean/ILean/C/native/plugin/setup families across generations under batch and server; missing files and one initializer mismatch are selected controls.",
 102:"Kill concurrent cache restore/publish at mapping and artifact-rename phases and retry corrupt objects; the real Lake kill was during elaboration before cache publication.",
 105:"Interrupt every actual Cargo/Charon/Aeneas/Lake/Lean stage and descendants, then reject late output via Anneal generation fencing; the real Charon stop covers one output phase.",
 108:"Check real cross-component lock order among preparation, cache, publication, restart and GC under bounded pauses; one Lake cache writer kill is a partial concurrency cell.",
 109:"Inject bounded memory/disk/fd/process exhaustion and recover last-good state; writer kill and RSS caps did not exercise these exhaustion classes.",
 120:"Prune prepared modules and then test new imports, tactics, macros, native plugins and scratch documents; the plugin fixture covers selected operation-dependent requirements.",
 123:"Connect real path aliases to module/document/cache identity and two intentional workspaces; APFS Lean imports and overlayfs byte lifetime do not establish Anneal routing.",
 124:"Exercise mapped live Lean artifacts and worker cleanup on every supported native filesystem; APFS Lean and cached Linux overlayfs bytes do not cover native ext4/XFS, Windows or network shares.",
 125:"Vary native plugin search paths, revision/ABI compatibility and initializer state with loaded-binary attestation; v1/v2 and mismatch cases are a bounded direct Lean/Lake witness.",
 131:"Rebuild captured Rust→Charon→Aeneas model inputs independently before fresh proof checking; two Lean versions still share a tiny prebuilt Dep artifact within each tuple.",
 132:"Calibrate source-level obligations, generated declarations and diagnostics with comparator mutants on broader cross-tool cases; two-version Lean theorem/axiom/goal equality is narrow.",
 135:"Run pairwise/higher-order source/import/cache/launch/lifecycle mutation matrix in the integrated Rust-to-proof pipeline; the Lean two-version split tests only selected axes.",
 136:"Reproduce highest-consequence findings on an independent machine/operator and selected compatible upgrade tuple; 4.29 versus 4.30-rc2 is two local cached versions, not an upgrade migration.",
 145:"Execute full identity ablation through actual Cargo→Charon→Aeneas→Lake→Lean→MCP responses; finite counterexamples cover four weakened tokens and selected ABA schedules only.",
 147:"Vary same/older/newer mtimes, byte-identical artifact rebuild and changed external model with unchanged Aeneas output, querying old/new workers; source-only and OLean-only cases are now real for two Lean pins.",
 148:"Compare Charon and Aeneas outputs with calibrated semantic comparator over process/order/flags/revision and downstream Lean cost; new Charon collisions are output-integrity witnesses.",
 150:"Complete operation-specific prepared archive inputs for lake serve/setup-file/InfoView/RPC/native plugin under read-only consumption; this tiny Lake/plugin matrix covers selected paths.",
 151:"Kill writers during actual cache mapping/artifact publication and compare conflicting shared-package writers with isolated frozen producer; the observed kill preceded publication.",
 158:"Replay cross-tool golden cases across selected compatible upgrades and explicitly test deletion of each workaround; local Lean 4.29/4.30-rc2 checks are separate within-version comparisons.",
 159:"Continue N01–N12 simple-alternative controls in a real integrated harness, especially generated-proof ownership and native shared-writer conflict; new source/import refresh and model counterexamples remain bounded.",
}

SUGGESTION = {
 "C04":("complete","All three requested direct Lean launch modes, watcher/reopen/new/fresh worker and fresh batch compared at the pinned small imported-definition fixture; larger graphs remain I050."),
 "D02":("partial","A copied B workspace and shared warmed target produced a stale path-sensitive generated constant; a general unsaved overlay algorithm was not tested."),
 "D03":("partial","Warm Cargo reported Fresh but selected charon cargo calls regenerated an absent or sentinel LLBC; other wrappers/targets remain."),
 "D06":("partial","A real Charon process was killed at a controlled second-output FIFO; full descendant cleanup and every extraction stage remain."),
 "F06":("partial","Missing OLean/ILean/C/plugin operation checks and an initializer mismatch server crash were run; complete prepared server artifact family remains."),
 "F08":("partial","Three server modes and setup-file missing-import exit-0 controls distinguish setup completion from ready proof; no integrated handshake was implemented."),
 "F11":("partial","Real Lake cache writer was killed during elaboration and repaired; cache mapping publication itself was not interrupted."),
 "N03":("partial","Watcher, new-file open, close/reopen and fresh worker were tried in three supported launch modes; already-open worker stayed stale in this fixture."),
}

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def read_csv(path: Path) -> list[dict[str,str]]:
    with path.open(newline="") as f:
        return list(csv.DictReader(f))

def write_csv(path: Path, rows: list[dict[str,object]]) -> None:
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]))
        writer.writeheader(); writer.writerows(rows)

def main() -> None:
    issue=json.loads((HERE/'issue-scope-snapshot.json').read_text())
    b30=issue['3730']['body']; b31=issue['3731']['body']; c31=issue['3731']['comments'][0]['body']
    head30=re.findall(r'^### ([A-Z]\d{2})\.',b30,re.M)
    head31=re.findall(r'^\*\*(I\d{3})\s+[—-]',b31,re.M)+re.findall(r'^\*\*(I\d{3})\s+[—-]',c31,re.M)
    cross_text=c31.split('## Complete #3730 → #3731 crosswalk',1)[1]
    cross_issue=re.findall(r'^\| ([A-Z]\d{2}) \| [^\n]* \| (I\d{3}[^|]*) \|$',cross_text,re.M)
    assert len(head30)==len(set(head30))==174
    assert head31==[f'I{i:03d}' for i in range(1,160)]
    assert len(cross_issue)==len({x[0] for x in cross_issue})==174
    assert set(head30)=={x[0] for x in cross_issue}

    prior=read_csv(PRIOR/'investigation-final.csv')
    old_cross=read_csv(PRIOR/'3730-crosswalk-final.csv')
    assert len(prior)==159 and [r['id'] for r in prior]==head31
    assert len(old_cross)==174
    old_map={r['3730_id']:set(r['3731_destinations'].split(';')) for r in old_cross}
    for key,dest in cross_issue:
        assert set(re.findall(r'I\d{3}',dest))==old_map[key],key

    review=[]; inventory=[]; mapped=defaultdict(list)
    for name,(ids,scope,boundary) in sorted(P.items()):
        package=REPORTS/name
        report,problems=reference._load_report(package)
        assert report and not problems,(name,problems)
        files=sorted(p for p in package.rglob('*') if p.is_file())
        for p in files:
            data=p.read_bytes();kind='binary';detail='opaque'
            if p.suffix.lower()=='.json':
                try:
                    json.loads(data);kind='json';detail='parsed'
                except (json.JSONDecodeError,UnicodeDecodeError) as exc:
                    kind='json-invalid-specimen';detail=f'{type(exc).__name__}: {str(exc)[:100]}'
            elif p.suffix.lower()=='.csv':
                detail=f'{len(read_csv(p))} data rows';kind='csv'
            else:
                try:
                    txt=data.decode('utf-8');kind='utf8';detail=f'{txt.count(chr(10))} lines'
                except UnicodeDecodeError:pass
            inventory.append({'package':name,'relative_file':p.relative_to(package).as_posix(),
                              'bytes':len(data),'sha256':sha(data),'inspection':kind,'detail':detail})
        review.append({'package':name,'reviewed_ids':';'.join(f'I{x:03d}' for x in ids),
                       'actual_executed_or_source_scope':scope,'boundary':boundary,
                       'file_count':len(files),'bytes':sum(p.stat().st_size for p in files),
                       'validator':'reference._load_report: valid'})
        for n in ids:mapped[n].append(name)
    write_csv(HERE/'package-review-v2.csv',review)
    write_csv(HERE/'file-inventory-v2.csv',inventory)

    rows=[]
    for r in prior:
        n=int(r['id'][1:]); add=mapped[n]
        status='partial' if n==3 else r['status']
        if n==49:status='complete'
        residual=DELTA.get(n,r['specific_remaining_delta'])
        scope=' | '.join(P[name][1]+' Boundary: '+P[name][2] for name in add)
        rows.append({**r,'latest_experiment_packages':';'.join(add),'status':status,
                     'latest_evidence_scope_and_limit':scope,'specific_remaining_delta':residual})
    assert len(rows)==159
    write_csv(HERE/'investigation-final-v2.csv',rows)
    byid={r['id']:r for r in rows}

    cross=[]
    for r in old_cross:
        key=r['3730_id']; dest=r['3731_destinations'].split(';')
        statuses=[byid[x]['status'] for x in dest]
        if all(x=='complete' for x in statuses):status='complete'
        elif any(x in ('complete','partial') for x in statuses):status='partial'
        elif all(x=='conditional' for x in statuses):status='conditional'
        else:status='not-run'
        # Preserve prior suggestion-specific distinctions unless new execution
        # directly changes that suggestion's distinguishing method.
        if r['status'] in ('not-run','conditional','complete') and key not in SUGGESTION:
            status=r['status']
        basis=r['suggestion_scope_basis']
        if key in SUGGESTION:status,basis=SUGGESTION[key]
        packages=';'.join(dict.fromkeys(p for d in dest for p in byid[d]['latest_experiment_packages'].split(';') if p))
        if key=='N11':exact='No residual for Lean-level no-goals falsification; Rust/Anneal coverage remains under I129/I137/I159.'
        elif key=='C04':exact='No residual for the pinned direct-Lean three-launch-mode counterexample; real Anneal integration and broader graph behavior remain under I050/I157.'
        else:exact='; '.join(d+': '+byid[d]['specific_remaining_delta'] for d in dest)
        cross.append({**r,'status':status,'destination_statuses':';'.join(statuses),
                      'latest_experiment_packages':packages,'suggestion_scope_basis':basis,
                      'specific_remaining_delta':exact})
    assert len(cross)==174
    write_csv(HERE/'3730-crosswalk-final-v2.csv',cross)
    suite=read_csv(PRIOR/'remaining-local-experiments.csv')
    suite_packages={
      'L01':'anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2',
      'L02':'anneal-3730-charon-warm-target-controls-2026-09-29',
      'L03':'anneal-3730-annotation-subject-boundary-matrix-2026-09-29',
      'L04':'anneal-3730-projection-macro-doccomment-patch-matrix-2026-09-29',
      'L05':'anneal-3730-lean-artifact-layouts-v4-30-0-rc2',
      'L06':'anneal-3730-lean-rpc-lifetimes-v4-30-0-rc2',
      'L07':'anneal-3730-generation-recovery-2026-09-29;anneal-3730-charon-concurrency-interruption-2026-09-29;anneal-3730-lake-writer-recovery-2026-09-29',
      'L08':'anneal-3730-charon-concurrency-interruption-2026-09-29',
      'L09':'anneal-3730-aeneas-identity-manifest-2026-09-29',
      'L10':'anneal-3730-lake-prepared-contract-2026-09-29;anneal-3730-lean-cross-version-equivalence-v4-29-v4-30-rc2-2026-09-29',
      'L11':'anneal-3730-lake-writer-recovery-2026-09-29',
      'L12':'anneal-3730-resource-economics-2026-09-29;anneal-3730-retention-economics-v4-30-0-rc2',
      'L13':'anneal-3730-lake-plugin-artifact-identity-v4-30-0-rc2',
      'L14':'anneal-3730-real-lean-filesystem-lifetimes-2026-09-29',
      'L15':'anneal-3730-acceptance-oracle-matrix-2026-09-29;anneal-3730-lean-cross-version-equivalence-v4-29-v4-30-rc2-2026-09-29',
      'L16':'anneal-3730-architecture-contracts-2026-09-29;anneal-3730-upstream-api-projection-precedents-2026-09-29',
      'L17':'anneal-3730-identity-state-mutation-model-2026-09-29',
      'L18':'anneal-3730-lean-cross-version-equivalence-v4-29-v4-30-rc2-2026-09-29',
    }
    assert len(suite)==18 and set(suite_packages)=={r['suite'] for r in suite}
    suite_rows=[]
    for r in suite:
        pkgs=suite_packages[r['suite']].split(';')
        assert all((REPORTS/p/'REPORT.md').is_file() for p in pkgs)
        suite_rows.append({'suite':r['suite'],'ids':r['investigation_ids'],
                           'bounded_packages':';'.join(pkgs),
                           'disposition':'bounded component/model execution; integration and listed gates remain',
                           'residual_from_original_suite':r['required_evidence_boundary']})
    write_csv(HERE/'suite-followup-v2.csv',suite_rows)
    local_gaps=[
      ('R01','I041-I050;I091;I147','Direct Lean/Lake transitive import, option, macro and plugin changes across old/new workers, with richer RPC dereference/release and causally delayed replies.','Use cached 4.29/4.30-rc2 binaries, tiny modules, one server at a time; still no Anneal envelope.'),
      ('R02','I073-I080;I105;I148','Extend pinned Charon process controls to lib/bin/test/feature and host-target selection, source reorder/flags, and regular-file output-phase interruption with request-private manifests.','Small crates, at most two processes and private targets; not a same-process library API.'),
      ('R03','I082-I088;I148;I149','Extend one-shot Aeneas CLI external-model/schema and declaration/range manifest controls, then batch-check emitted Lean against a small independent Rust input.','Use installed CLI only; in-memory calls and registered OCaml library model remain gated.'),
      ('R04','I089-I104;I108-I109;I150-I151','Interrupt Lake artifact-cache publication at output-map/artifact writes and retry damaged objects; test conflicting writable package directories separately from shared immutable cache.','Scratch cache and two tiny consumers, capped disk/processes; product archive still absent.'),
      ('R05','I113-I119;I139;I146;I153-I154','Guarded 1/2/4 worker workload and short soak with representative imports, process-tree physical footprint and contamination sentinels; preserve each skipped cell if memory guard fires.','8 GiB host, free-memory and disk preflight, capped duration; no Mathlib-scale inference.'),
      ('R06','I126-I136;I158-I159','Manual pinned Rust→Charon→Aeneas→Lean golden vertical with source/import/obligation negative controls and fresh clean rebuild, then selected cached two-version replays.','Small fixed obligations and exact binary hashes; no Anneal generated service or independent machine.'),
      ('R07','I025-I032;I059-I063','Extend direct Lean diagnostic/position probes and illustrative Rust macro/doc-comment maps to a source-owned edit/diagnostic specimen matrix.','Can remain a model/direct component probe; actual editor UI and Anneal source map remain gated.'),
    ]
    write_csv(HERE/'remaining-local-experiments-v2.csv',[
      {'gap':g,'investigation_ids':ids,'bounded_next_experiment':work,'resource_and_evidence_limit':limit}
      for g,ids,work,limit in local_gaps])
    gated=[
      ('G01','I081;I086','Same-process Aeneas reset, concurrency and in-memory handoff need a compatible OCaml/Dune/opam or prebuilt library API not installed in this task.','User selects/authorizes non-local dependency scope or supplies a compatible prebuilt API.'),
      ('G02','I141','Human understanding of freshness/failure cannot be simulated by another agent.','Recruit human participants and choose a study protocol and UI.'),
      ('G03','I143','Durable remote execution is conditional on a measured need and selected remote target.','Choose remote target, persistence promise and failure budget after local measurements.'),
      ('G04','I124','Native ext4/XFS, Windows/network filesystem and indexer behavior exceed host APFS plus cached Ubuntu overlayfs.','Select supported target and provide/approve another platform image or machine.'),
      ('G05','I003;I059-I063;I072','Actual Volar/Razor/client and Lean MCP adapter process comparisons require clients/services not installed in this checkout.','Select clients/adapters and installation scope; pinned source and toy projection remain partial evidence.'),
      ('G06','I010;I012;I057-I072;I137-I140;I152;I155-I157','The checkout has no complete Anneal V2 editor/MCP bridge, Rust-hosted Lean projection service, shared workspace authority or batch/live engine.','Implement a minimal product vertical, then run the exact row residuals through it.'),
      ('G07','I001;I004;I008;I142;I144;I159','Architecture adoption and upstream patch acceptance require product decisions after real workload evidence.','Choose topology, thresholds and accepted contract in Anneal design review.'),
    ]
    write_csv(HERE/'gated-work-v2.csv',[
      {'gate':g,'investigation_ids':ids,'exact_unavailable_or_conditional_dimension':reason,'unblock_condition':condition}
      for g,ids,reason,condition in gated])
    validation={
      'snapshot_utc':issue['snapshot_utc'],
      'issue_3730_state':issue['3730']['state'],'issue_3731_state':issue['3731']['state'],
      'issue_3730_body_sha256':sha(b30.encode()),
      'issue_3730_comment_sha256':sha(issue['3730']['comments'][0]['body'].encode()),
      'issue_3731_body_sha256':sha(b31.encode()),
      'issue_3731_comment_sha256':sha(c31.encode()),
      'investigation_rows':len(rows),'investigation_statuses':dict(Counter(r['status'] for r in rows)),
      'crosswalk_rows':len(cross),'crosswalk_statuses':dict(Counter(r['status'] for r in cross)),
      'complete_investigations':[r['id'] for r in rows if r['status']=='complete'],
      'complete_suggestions':[r['3730_id'] for r in cross if r['status']=='complete'],
      'new_package_count':len(P),'new_packages':sorted(P),
      'new_inspected_file_count':len(inventory),'new_inspected_bytes':sum(int(x['bytes']) for x in inventory),
      'source_prior_investigation_sha256':sha((PRIOR/'investigation-final.csv').read_bytes()),
      'source_prior_crosswalk_sha256':sha((PRIOR/'3730-crosswalk-final.csv').read_bytes()),
      'suite_rows':len(suite_rows),'remaining_locally_executable_suites':len(local_gaps),'gate_groups':len(gated),
    }
    (HERE/'validation-v2.json').write_text(json.dumps(validation,indent=2)+'\n')
    print(json.dumps({k:v for k,v in validation.items() if k!='new_packages'},indent=2))

if __name__=='__main__':main()
