#!/usr/bin/env python3
"""Rebuild this bounded post-interim audit from the preserved issue ledger.

Mappings below were curated from report methods and boundaries, not title matches.
This script does not execute report probes or modify the source audits.
"""
import csv,hashlib,json,sys
from collections import Counter,defaultdict
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPORTS=HERE.parents[1]
INTERIM=REPORTS/'anneal-3730-3731-gap-audit-interim-2026-09-29'/'support'
sys.path.insert(0,str(REPORTS.parent/'tools'))
import reference

P={
 'anneal-3730-acceptance-oracle-matrix-2026-09-29':(
  [126,127,128,129,130,131,132,134,135,144,159],
  'Two direct Lean runs: exact imported artifact/fresh proof, weak/admitted/axiom/wrong-import/missing-claim controls, killed consumer, benign tactic IO and fake-token redaction.',
  'Synthetic Lean proposition and local LSP only; no Anneal obligation graph, human trial or independent kernel.'),
 'anneal-3730-aeneas-identity-manifest-2026-09-29':(
  list(range(82,89))+[148,149,156,158],
  'Pinned one-shot Aeneas CLI input/flag/schema matrix, complete file/declaration manifest, stale output and partial-sorry failure.',
  'No same-process library call, registered external-model mutation, authenticated cross-layer mapping or second release.'),
 'anneal-3730-architecture-contracts-2026-09-29':(
  [1,2,4,5,6,7,8,142,144,159],
  'Pinned architecture precedent/source comparison and three runnable toy process topologies with failure, restart and collision controls.',
  'Toy hash-and-sleep backend; not matched real Charon/Aeneas/Lean cost, upstream patch, or adopted design.'),
 'anneal-3730-charon-scaling-subject-closure-2026-09-29':(
  [9,15,16,73,75,76,78,79],
  'Pinned Charon/Cargo workspace: 1/32/192 root closure, feature/build-script/include input perturbations and wrong-member partial LLBC after failed multi-library request.',
  'Saved sources/fresh targets only; no overlay, warm-target proof, concurrent producers or full semantic normalization.'),
 'anneal-3730-generation-recovery-2026-09-29':(
  list(range(51,56))+list(range(105,113))+[121,122],
  'Direct filesystem/process fixture with nine SIGKILL phases, multi-file staging, late completion, locks/GC/restart and reconciliation.',
  'Synthetic backend and tiny files; not actual Cargo/Charon/Aeneas/Lake/Lean process groups or crash-durable product state.'),
 'anneal-3730-independent-vertical-reproduction-2026-09-29':(
  [136],
  'Second worker wrote a new driver and reran A/F/B live/batch/gated-late controls; 33/33 exact comparison fields matched.',
  'Same host/toolchain and prior source exposure; no independent machine/operator blind study or compatible-upgrade matrix.'),
 'anneal-3730-lake-prepared-contract-2026-09-29':(
  list(range(89,105))+[120,125,150,151],
  'Tiny two-package Lean/TOML clean and relocated prepared Lake fixture, no-build checks, isolated home/denied loopback, native facet and cache wrong-object/truncated-map controls.',
  'No real Anneal archive, server query, complete plugin/native family, network syscall trace, concurrent restore or full integrity oracle.'),
 'anneal-3730-lean-artifact-layouts-v4-30-0-rc2':(
  [35],
  'Three Lean/Lake module-layout approximations over identical two-claim/helper proofs at model sizes 1/128; edits, failure isolation, worker/import costs and visibility.',
  'No actual embedded Rust annotation layout, large imports, parallel scheduler or more than two workers.'),
 'anneal-3730-lean-rpc-lifetimes-v4-30-0-rc2':(
  [41,42,43,44,45,47],
  'Direct Lean RPC session across edit/cancel/close/reopen/new server, killed worker, late old transport reply and retained separate-URI old source.',
  'No ctx dereference/release/expiry or actual Anneal envelope; successful late old response used separate transports.'),
 'anneal-3730-multiclient-editor-contract-2026-09-29':(
  [57,58,62,64,65,66,67,68,69,71,152,155,156,157],
  'One direct Lean stdio connection plus two logical local clients: unsaved source, versioned goal/diagnostics, CAS retry, dropped local event/poll, restart/rename and direct cancellation.',
  'No actual MCP transport, editor extension, separate clients, diagnostic multiplexing or real Anneal bridge.'),
 'anneal-3730-partial-elaboration-queries-v4-30-0-rc2':(
  [41,43,46,129],
  'Direct Lean valid declarations around unfinished proof, unknown tactic, heartbeat timeout and recoverable syntax error; goal positions, diagnostics and batch failures.',
  'No integrated Anneal status; nested/macros/EOF and stronger concurrency not tested. I046 requested direct-Lean fixture is satisfied.'),
 'anneal-3730-platform-filesystem-boundary-2026-09-29':(
  [124],
  'Two trials each on host APFS and cached Ubuntu/OrbStack Linux overlayfs: descriptor/rename/unlink/flock and 2,400 sampled reads per trial.',
  'No mapped Lean artifacts, native Linux ext4/XFS, Windows/network filesystem, indexer or crash durability.'),
 'anneal-3730-projection-provenance-2026-09-29':(
  [25,26,27,29,30,31],
  'Real Charon/Aeneas coarse spans plus invented doc-comment exact-byte/UTF-16 projection, multi-range CAS and synthetic edit rejection.',
  'No Anneal parser/source map, actual hover/rename, true one-to-many obligation routing or production generator.'),
 'anneal-3730-resource-economics-2026-09-29':(
  list(range(113,120))+[139,146,153,154],
  'Guarded two-Lake-consumer cold/warm run and two-server four-edit sentinel, sampled RSS/phys_footprint/disk with clean shutdown.',
  'Tiny fixtures, no Anneal generated project, Mathlib, high-worker sweep, long soak, PSS or peak-between-polls proof.'),
 'anneal-3730-server-topology-v4-30-0-rc2':(
  [44,45,153],
  'One direct Lean watchdog versus two on conflicting same-named Dep imports; direct session invalidation after close/reopen and summed RSS.',
  'No MCP broker, Lake launch matrix, 4/8 document sweep, unique physical memory or delayed internal-worker response.'),
}

OVERRIDE={
 4:'Repeat the one-shot/per-project/broker comparison with actual Charon/Aeneas/Lean work, matched isolation, startup, restart and physical-resource measurements; the new timing rank is toy-only.',
 8:'Pin the upstream API gap inventory to executable call sites and compare a minimal adapter with a small upstream patch under the same acceptance oracle.',
 15:'Measure dependency-scoped versus global invalidation after unrelated/newly discovered inputs and verify saved work against a clean Charon oracle; the root-closure fixture only exposes dependencies.',
 35:'Real embedded-annotation grouping and representative imports/options/plugins remain for product application; the requested bounded Lean/Lake layout comparison itself was executed, but its approximations do not establish the Anneal layout choice.',
 41:'Causally gated version/query interleavings and a chosen client fence under real worker replacement; RPC and partial-file reports add direct observations but no complete race matrix.',
 42:'Separate parsing/import/elaboration/async delays with ready-at-position and whole-file status; one gated cancellation and heartbeat timeout are not the full readiness matrix.',
 43:'Nested tactics, combinators, macros, EOF/whitespace and rich-vs-plain RPC position grid beyond the sampled valid tactic columns.',
 44:'Dereference ctx objects after edit/cancel/close/restart, release them, and measure expiry; the new report mainly tests session validity.',
 45:'Internal worker replacement with deliberately delayed successful old response, reused request IDs on one transport and forced-versus-clean termination; two-server late reply is narrower.',
 46:'No residual for the requested direct Lean partial-file fixture at this pin: all four named error classes, before/after goals, diagnostics and failing batch status were observed. Product integration is separately tracked in I129/I137.',
 47:'Measure actual retained historical-goal storage/latency through rapid edits and expiry; separate-URI old text only proves a possible construction.',
 51:'Repeat multi-file staged publication with actual generated Lean/LLBC/OLean artifact family, paused readers and crash recovery; new direct filesystem fixture is synthetic.',
 52:'Prepare final versus moved Lake/Anneal generations across manifests, traces, setup, native libraries and retained workers; the synthetic rename and small Lake relocation cover subsets.',
 53:'Causally late Charon/Aeneas/Lake/Lean outputs tested separately for source, compiled artifacts, diagnostics and cache insertion, beyond synthetic child/stale-pointer fence.',
 54:'Fail real extraction, translation, build and server stages with visible last-good/provisional state and rollback; the new kill matrix uses synthetic stages.',
 55:'Shrink and delete a selected real Aeneas/Lean output/obligation set with reused names and fresh verifier; synthetic tree and one-shot Aeneas clean oracle are narrower.',
 67:'Actual MCP transport-loss retries for edit/worker-create/check-start with durable bounded dedup expiry and CAS; local broker only models one edit response.',
 76:'Concurrent actual compilation units across targets/host-target/features/crate-name collisions with LLBC output ownership; the new workspace request wrote a wrong-member partial file on failure.',
 78:'Interrupted/failing Charon output with explicit successful-request echo, schema/subject/completeness validation and atomic publication; one failed workspace case wrote partial wrong-member LLBC.',
 82:'Compiled external-model registry, normalization and a genuine second binary/library revision with collision controls; new CLI matrix covers LLBC/schema/options and copied runtime library.',
 83:'External-model/trait-declaration edits, a measured finer-grained cache prototype and semantic oracle; new whole-crate CLI controls cover function/type/impl/recursive-group effects.',
 84:'Reorder/module move and unrelated-edit tests of Lean names/signatures/proof context under actual elaboration; helper insertion/source locations alone are insufficient.',
 85:'Registered user-maintained external model, overwrite collisions and atomic generation publication; new manifest/deletion/reused-destination/sorry-failure controls cover only CLI ownership.',
 87:'Authenticated Charon item → Aeneas declaration/range mapping with source-map completeness and comparison to newer translation.json; emitted comments are lexical hints only.',
 88:'Warnings/crashes/cancellation and repeated-request residual state with structured diagnostic origins across pins; new schema/loader/partial-output errors are one-shot.',
 89:'Actual Anneal prepared archive from empty home/cache, server and first-goal write tracing under enforced read-only dependencies; new small Lake tree covers relocated batch/no-build only.',
 90:'Duplicate/name/order/version/rename package-graph collisions beyond the two-config small package; exact consumer identity still needs a graph matrix.',
 92:'Server no-build path against missing configs, malformed manifests and all incomplete artifact families; current fixture checked selected setup/batch/native cases only.',
 93:'Dynamic Lean configuration/environment inputs and changed package graph under Lean versus TOML, beyond one equal consumer theorem and trace difference.',
 94:'Read-only prepared consumer behavior on a selected later compatible Lean/Lake tuple; current prepared fixture is 4.30-rc2 only.',
 97:'Cache-key false-hit/false-miss ablations across source/model/tool/flags/path plus independent integrity verification; a valid wrong-object hit exposes one false acceptance.',
 98:'Mixed or truncated cross-generation OLean/ILean/native/setup/plugin family under server and batch; current native facet and truncated cache map are selected cells.',
 99:'Independent clean versus prepared comparison of declarations, assumptions, navigation, tactic states and imported artifacts; current tiny fixed consumer/axiom agrees only on one theorem.',
 101:'Real generated Anneal consumer relocated after server preparation with original producer inaccessible; test native/setup/diagnostics paths and retained workers beyond small Lake batch.',
 102:'Interrupted concurrent restore/download/extract/publish with wrong-identity/corrupt-object recovery; truncated cache mapping is only one parser failure.',
 104:'Trace producer/consumer network and filesystem attempts under isolated home/cache while denying external access; loopback denial establishes one control, not full offline closure.',
 105:'Per-stage process-group cancellation through actual Cargo/Charon/Aeneas/Lake/Lean and descendant cleanup; new SIGKILL phases exercised synthetic children.',
 106:'Queued real diagnostics/progress/exits after cancellation with request/worker correlation and publication fences; synthetic late completion is narrower.',
 107:'Shared actual build with multiple consumers, one cancellation and one failure plus reference-count/fan-out; synthetic ownership model alone is insufficient.',
 108:'Real lock ordering across Lake/Anneal prepare/publish/cache/restart/GC with injected pauses and bounded waits; current filesystem locks are a synthetic state fixture.',
  109:'Bounded real time, memory, disk, descriptor and process-slot exhaustion with recovery and last-good preservation; kill and small RSS controls do not cover exhaustion.',
  110:'Forced actual Lean worker/watchdog, Anneal and build-process kills with reconstruction from authoritative source/imports; new OS kills target a synthetic publisher.',
  111:'Measured edit-storm tail latency/starvation across slow documents, multiple agents and batch load; short resource fixture has four edits only.',
  112:'Dropped/duplicated/reordered actual watcher/MCP/LSP events with reconciliation; synthetic watcher and local broker events are not transport delivery.',
  114:'Guarded correctness/throughput/latency/CPU/physical-memory/disk sweep beyond two tiny Lake consumers, with realistic imports and host-budget bounds.',
  116:'Long edit/query/open/close/restart soak with retention/leak classification; new four-edit/two-server run is short.',
  117:'PSS or unique process-tree footprint and file-cache sharing for workers/plugins/watchdogs; phys_footprint samples improve on RSS sums but not this full accounting.',
  120:'After pruning, test new imports/tactics/macros/plugins and scratch documents; one native facet/load is operation-specific but not extensibility-complete.',
  121:'GC leases for actual live workers, pending queries, scratch forks, later opens and replay records; new lease/GC fixture uses synthetic generations.',
  122:'Repeated crash/restart cleanup with durable owner identity and bounded orphan reclaim in an actual Anneal/Lake workspace; synthetic process fixture alone is insufficient.',
  124:'Open memory-mapped Lean artifacts and full worker cleanup on each supported native filesystem; Windows/indexer and network filesystem behavior remain conditional on product scope. New Linux data is OrbStack overlayfs only.',
  125:'Native plugin lookup, revision, ABI and initializer replacement with attested loaded binary; current fixture checks one explicit dynlib facet/load.',
  126:'Lake configuration, Lean macros/native extensions and enforced containment/resource limits; a benign run_tac write adds one execution boundary to prior Cargo/Lean callbacks.',
  129:'Machine result taxonomy integrated with actual Anneal source/model/obligation identities, separating reachable goal, file elaboration, admissions, pending/failed generation and Rust-level coverage.',
  130:'Claim-relative axiom/admission/native/model taint propagated through theorem callers and reused artifacts/adapters; new cheat/sorry controls are one-hop.',
  131:'Clean dependency rebuild or independent artifact/kernel audit over real captured Rust→Charon→Aeneas inputs; fresh Lean processes still share pinned model OLean and toolchain.',
  132:'Calibrate declaration/semantic/obligation and cross-tool diagnostic comparators on broad generated cases; new seven-control matrix catches weak/admitted/axiom/missing/wrong import in one Lean fixture.',
  134:'Actual in-flight Charon/Aeneas/Lake/Lean edits/rebuilds with request/worker identities and barriers; new gate/kill remains a synthetic publisher or isolated Lean consumer.',
  135:'Pairwise/higher-order source/import/cache/launch/lifecycle matrix in real pipeline with seeded wrong subject/assumption; new negative controls cover selected one-factor cases.',
  136:'A genuinely independent environment/operator without prior source exposure, plus selected compatible toolchain upgrade matrix; new second driver used same host/Lean and was not blind.',
  139:'Actual parallel Anneal generated-project tests combining model edit/scratch/restart/cleanup and host-budget limits; new two-Lake-consumer plus two-server samples are separate analogs.',
  142:'Matched real-workload adoption gates for reuse, fine invalidation, incremental projection, shared broker and history; current toy topology gives mechanism/failure costs but no backend benefit.',
  144:'After remaining real integration/workload evidence, synthesize explicit v2 interface choices and smallest regression probes; new decision ledgers do not adopt a design.',
  148:'Sequential/concurrent Aeneas and Charon mode/flag/layout matrix with calibrated semantic comparator and downstream Lake/Lean cost; new Aeneas CLI cases cover byte sensitivity only.',
  149:'Proven Rust→Charon→Aeneas→Lean→obligation identities and one-to-many graph consumed by navigation/editing; new manifest inventories exact files/declaration heads but null proven mappings.',
  150:'Complete operation-specific prepared inputs for lake serve, setup-file, InfoView/RPC, native/plugin use and ownership in a real generated archive; current small Lake fixture covers selected operations.',
  151:'Conflicting simultaneous Lake writers and controlled kill at output/trace/cache publication with full inspection; current wrong-cache-object and prior writer-scale cases are incomplete.',
  152:'Actual MCP subscriptions/listen versus polling under delayed/dropped delivery, reconnect and state reconciliation; new local event model is not MCP transport.',
  153:'Matched one-watchdog versus N-server plus MCP broker/adapters at 1/2/4/8 documents with scratch churn and physical-memory cost; current direct-Lean 1/2 tests are small.',
  154:'Per-test/per-fixture/per-suite contamination matrix including plugins, phase ordering and worker restarts; new two-workspace sentinels are a narrow direct-Lean control.',
  155:'Actual Rust editor host open/change/save/rename/close through Anneal projection and hidden Lean cleanup; new invented //% host in a local broker tests only lifecycle shape.',
  156:'Versioned executable Charon/Aeneas/Lean capability descriptors with real adapter fallback and unsupported-call behavior; one-shot Aeneas and local broker descriptors are partial.',
  157:'One actual Anneal engine driven by current batch CLI and repeated in-process live shell with cancellation/reconstruction and fresh exact-input oracle; current Python prototypes are separate.',
  158:'Retained cross-tool replay on selected compatible upgrades and explicit obsolete-workaround deletion probes; current Aeneas replay and two-Lean-version direct-server case are slices.',
  159:'Execute remaining N01–N12 simple alternatives in relevant real integrated harnesses, especially supported refresh, native shared-writer conflict, generated proof ownership and cancellation; current counterexamples are scoped.',
}

COMPLETE={46}
CONDITIONAL={81:'OCaml/Dune/opam toolchain not installed; same-process Aeneas needs user-approved non-local dependency scope.',
             141:'Requires actual human participants and interface comprehension trial; no agent card check substitutes.',
             143:'Remote durable job is conditional on an actual measured local workflow need; no remote deployment justified by this corpus.'}
PROMOTE_PARTIAL={2,4,8,35,65,66,67,68,69,71,124,139,142,152,155}
SUGGESTION_OVERRIDES={
 'B11':('not-run','No actual LSP code action or rename transaction was executed; projection edit rejection is only a prerequisite.'),
 'B12':('not-run','No mapped hover/completion/token/signature-help/inlay-hint operation was executed.'),
 'C04':('not-run','The requested matched Lake/direct server launch-mode comparison is still absent at this cutoff.'),
 'C11':('not-run','No supported two-open-document unsaved-proof import was executed.'),
 'D01':('not-run','No saved-versus-unsaved Rust overlay comparison was executed.'),
 'D02':('not-run','No shadow-overlay path-sensitive compiler run was executed.'),
 'D03':('not-run','No warm Cargo target/Charon skip probe had completed by the snapshot cutoff.'),
 'D06':('not-run','No actual Charon process cancellation/descendant-cleanup run was executed.'),
 'E01':('conditional','Same-process Aeneas reuse requires the OCaml/Dune/opam dependency decision; one-shot CLI runs do not answer it.'),
 'E02':('conditional','Aeneas global-state reset in one process requires the OCaml/Dune/opam dependency decision.'),
 'E03':('conditional','Concurrent in-process Aeneas calls require the OCaml/Dune/opam dependency decision.'),
 'E10':('not-run','No compiled external-model registry mutation with unchanged Rust codegen was executed.'),
 'E11':('not-run','Whole-crate counterexamples were run, but no restricted finer-grained Aeneas cache prototype was built.'),
 'F03':('not-run','No later compatible Lake tuple received the prepared read-only consumer test.'),
 'F04':('not-run','No real Anneal archive was tested with a missing manifest.'),
 'F06':('not-run','No server readiness with an incomplete prepared artifact family was tested.'),
 'F08':('not-run','No matched build-complete versus server-ready handshake was executed.'),
 'F11':('not-run','No actual Lake artifact-cache writer was killed during publication.'),
 'G03':('not-run','No real MCP long-running task/progress/result lifecycle was executed.'),
 'G07':('not-run','No actual isolated tactic scratch trial or reusable pool was exercised.'),
 'G15':('not-run','No actual Rust-to-Lean-and-back navigation tool was exercised.'),
 'H08':('not-run','No real editor workspace-folder/project switch was exercised.'),
 'H09':('not-run','No real editor cancellation was propagated through an Anneal scheduler.'),
 'J02':('not-run','No complete cross-stage copied-byte attribution exists.'),
 'J05':('not-run','No prewarmed scratch pool scaling experiment was run.'),
 'J06':('not-run','No nested Cargo/Aeneas/Lake/Lean parallelism budget sweep was run.'),
 'J09':('not-run','No high-concurrency fault run with actual generated projects was performed.'),
 'J10':('not-run','No long-lived daemon soak or drift classification was performed.'),
 'J14':('not-run','The APFS/overlayfs semantics probe did not measure filesystem-specific resource scaling.'),
 'L09':('not-run','No installed Lean MCP adapter was exercised under Anneal conditions.'),
 'L10':('conditional','Aeneas library embedding depends on the unresolved OCaml/Dune/opam toolchain decision.'),
 'M03':('not-run','No second Charon version was selected for an upgrade checklist execution.'),
 'M04':('not-run','No second Aeneas version was selected for an upgrade checklist execution.'),
 'M06':('not-run','No workaround-deletion probe was run on a compatible upgraded tuple.'),
 'N03':('not-run','An existing Lean worker was not shown to refresh a changed import through a supported operation.'),
 'N08':('not-run','No real generated-Lean-as-canonical-proof-source ownership experiment was run.'),
 'N11':('complete','Weak, admitted, axiom and missing-obligation controls falsify no-goals-as-acceptance for the Lean-level claim; Rust-level coverage remains a separate investigation.'),
}

def read_rows(path):
    with path.open(newline='') as f:return list(csv.DictReader(f))
def write_rows(path,rows):
    with path.open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(rows[0]));w.writeheader();w.writerows(rows)

def main():
    old=read_rows(INTERIM/'investigation-gap-matrix.csv')
    assert len(old)==159 and [x['id'] for x in old]==[f'I{i:03d}' for i in range(1,160)]
    new_names=sorted(P)
    review=[];inventory=[];mapped=defaultdict(list)
    for name in new_names:
        ids,observed,boundary=P[name]
        path=REPORTS/name
        report,problems=reference._load_report(path)
        assert report and not problems,(name,problems)
        files=sorted(p for p in path.rglob('*') if p.is_file())
        for file in files:
            data=file.read_bytes(); rel=file.relative_to(path).as_posix()
            kind='binary';detail='opaque artifact'
            if file.suffix.lower()=='.json':
                json.loads(data);kind='json';detail='parsed'
            elif file.suffix.lower()=='.csv':
                records=read_rows(file);kind='csv';detail=f'{len(records)} data rows'
            else:
                try:
                    txt=data.decode('utf-8');kind='utf8';detail=f'{txt.count(chr(10))} lines'
                except UnicodeDecodeError:pass
            inventory.append({'package':name,'relative_file':rel,'bytes':len(data),
                'sha256':hashlib.sha256(data).hexdigest(),'inspection':kind,'detail':detail})
        review.append({'package':name,'reviewed_ids':';'.join(f'I{x:03d}' for x in ids),
            'actual_executed_or_source_scope':observed,'boundary':boundary,
            'file_count':len(files),'bytes':sum(p.stat().st_size for p in files),
            'validator':'reference._load_report: valid'})
        for n in ids:mapped[n].append(name)
    write_rows(HERE/'package-review.csv',review)
    write_rows(HERE/'file-inventory.csv',inventory)
    rows=[]
    for row in old:
        n=int(row['id'][1:]);added=mapped[n]
        status='partial' if row['disposition']=='partial execution' else 'not-run'
        if n in PROMOTE_PARTIAL:status='partial'
        if n in COMPLETE:status='complete'
        if n in CONDITIONAL:status='conditional'
        evidence=';'.join(x for x in [row['prior_corpus_pointers'],row['reviewed_new_packages'],';'.join(added)] if x)
        evidence=';'.join(dict.fromkeys(x for x in evidence.split(';') if x))
        residual=OVERRIDE.get(n,row['specific_remaining_delta'])
        if n in CONDITIONAL:residual=CONDITIONAL[n]
        scopes=' | '.join(P[name][1]+' Boundary: '+P[name][2] for name in added)
        rows.append({'id':row['id'],'section':row['section'],'title':row['title'],
           'requested_methods':row['requested_methods'],'requested_scope':row['requested_scope'],
           'prior_evidence_packages':row['prior_corpus_pointers'],
           'interim_experiment_packages':row['reviewed_new_packages'],
           'post_interim_experiment_packages':';'.join(added),
           'status':status,'new_evidence_scope_and_limit':scopes,
           'specific_remaining_delta':residual})
    write_rows(HERE/'investigation-final.csv',rows)
    cross_old=read_rows(INTERIM/'3730-crosswalk-disposition.csv')
    assert len(cross_old)==174 and len({x['3730_id'] for x in cross_old})==174
    byid={x['id']:x for x in rows}
    cross=[]
    for r in cross_old:
        dest=[x.strip() for x in r['3731_destination'].split(',')]
        assert all(x in byid for x in dest)
        statuses=[byid[x]['status'] for x in dest]
        if all(x=='complete' for x in statuses):status='complete'
        elif any(x in ('complete','partial') for x in statuses):status='partial'
        elif all(x=='conditional' for x in statuses):status='conditional'
        else:status='not-run'
        basis='Mapped destination evidence is scoped by its report; this suggestion is not inferred complete from a partial destination.'
        if r['3730_id'] in SUGGESTION_OVERRIDES:
            status,basis=SUGGESTION_OVERRIDES[r['3730_id']]
        exact='; '.join(x+': '+byid[x]['specific_remaining_delta'] for x in dest)
        if r['3730_id']=='N11':
            exact='No residual for the Lean-level falsification of no-goals-as-acceptance; full Rust/Anneal coverage remains under I129/I137/I159.'
        packages=';'.join(dict.fromkeys(p for x in dest for p in byid[x]['post_interim_experiment_packages'].split(';') if p))
        cross.append({'3730_id':r['3730_id'],'suggestion':r['suggestion'],
             '3731_destinations':';'.join(dest),'status':status,
             'destination_statuses':';'.join(statuses),
             'post_interim_experiment_packages':packages,
             'suggestion_scope_basis':basis,
             'specific_remaining_delta':exact})
    write_rows(HERE/'3730-crosswalk-final.csv',cross)
    manifest={'snapshot_utc':'2026-09-29 08:18 UTC','post_interim_package_count':len(new_names),
              'post_interim_packages':new_names,'inspected_file_count':len(inventory),
              'inspected_bytes':sum(int(x['bytes']) for x in inventory),
              'investigation_rows':len(rows),'investigation_statuses':dict(Counter(x['status'] for x in rows)),
              'crosswalk_rows':len(cross),'crosswalk_statuses':dict(Counter(x['status'] for x in cross)),
              'complete_ids':[x['id'] for x in rows if x['status']=='complete'],
              'source_interim_matrix_sha256':hashlib.sha256((INTERIM/'investigation-gap-matrix.csv').read_bytes()).hexdigest(),
              'source_interim_crosswalk_sha256':hashlib.sha256((INTERIM/'3730-crosswalk-disposition.csv').read_bytes()).hexdigest()}
    (HERE/'validation.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps({k:v for k,v in manifest.items() if k not in ('post_interim_packages',)},indent=2))
if __name__=='__main__':main()
