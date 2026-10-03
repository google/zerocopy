"""Aggregate completed experiment evidence; no compiler invocation."""
import json,sys
from probes import ROOT,AENEAS,RC2,REPO,snapshot
from real_sdk_lake import SDK
from guard import host_sample,processes
import subprocess

rows=[json.loads(x) for x in (ROOT/'runs.jsonl').read_text().splitlines()]
by_label={r['label']:r for r in rows}
success=['native-lake-smoke-target','native-lake-smoke-build','native-lake-smoke-setup',
 'native-lake-v1-audit','native-lake-v1-setup','native-lake-followup-baseline',
 'native-lake-followup-noop','native-lake-followup-edit','native-lake-followup-delete-output',
 'native-lake-v1-noop','20261003-112910-prefix','20261003-112910-build','20261003-112910-setup']
success += ['native-lake-v1-build-'+s for s in ['SdkIdentity','Config','ExpandOutputExpandOutput1d49e11e5683007f.Types','ExpandOutputExpandOutput1d49e11e5683007f.Funs','Anneal','Generated']]
failures=['native-lake-smoke-false','native-lake-v1-false','native-lake-v1-sorry',
 'native-lake-followup-bad-plugin','sdk-missing-stock-lake','sdk-missing-native-stock-lake','final-rc2-mismatch']
for label,expected in [(x,0) for x in success]+[(x,1) for x in failures]:
    r=by_label[label];assert r['exit']==expected and r['abort'] is None,(label,r['exit'],r['abort'])
assert 'does not depend on any axioms' in (ROOT/'records/native-lake-v1-audit.stdout').read_text()
assert "'sorry' tactic is forbidden" in (ROOT/'records/native-lake-v1-sorry.stdout').read_text()
assert 'incompatible header' in (ROOT/'records/final-rc2-mismatch.stdout').read_text()
after=snapshot('archive-final-after',content=True)
assert after==json.loads((ROOT/'archive-pristine-before.json').read_text()),'Archive content/metadata changed'
sdk_after=snapshot('sdk-final-after',root=SDK,content=True)
assert sdk_after==json.loads((ROOT/'real-sdk-overlay-before.json').read_text()),'SDK view content/metadata changed'
cells=[json.loads(x) for x in (ROOT/'cells.jsonl').read_text().splitlines()]
selected={r['case']:r for r in cells if r['case'] in set(success+failures)}
for case,row in selected.items():assert not row['shared_attempts'] and not row['network_attempts'],case
lsps=[]
for label in ['native-sdk-lsp-1','native-sdk-lsp-navigation-1']:
    r=json.loads((ROOT/'records'/(label+'.lsp.result.json')).read_text())
    assert r['result']=='pass' and r['exit']==0 and r['abort'] is None,label
    events=[json.loads(x) for x in (ROOT/'records'/(label+'.lsp.events.jsonl')).read_text().splitlines()]
    assert not any(x.get('blocked') or x['kind']=='network' for x in events),label
    assert not processes(r['pid']),'Own server still running'
    lsps.append({k:r[k] for k in ['label','result','elapsed_s','peak_sampled_rss_mib','min_memory_free_pct','min_disk_free_gib']})
for path in [ROOT/'records/native-lake-v1-sorry.pid',ROOT/'records/sdk-missing-native-stock-lake.pid']:
    assert not processes(int(path.read_text())),'Recent own child still running'
status=subprocess.run(['git','status','--porcelain'],cwd=REPO,text=True,capture_output=True,check=True).stdout
assert status=='',f'Source worktree changed: {status}'
summary={'completed_expected_command_checks':len(success)+len(failures),'guarded_commands_total':len(rows),
 'archive_unchanged':True,'sdk_view_unchanged':True,'source_worktree_clean':True,
 'guard_stops':[{k:r.get(k) for k in ['label','exit','abort','elapsed_s']} for r in rows if r.get('abort')],
 'selected_peak_rss_mib':round(max(s['rss_kib'] for r in rows if r['label'] in set(success+failures) for s in r['samples'])/1024,1),
 'selected_min_memory_free_pct':min(s['memory_free_pct'] for r in rows if r['label'] in set(success+failures) for s in r['samples']),
 'selected_min_disk_free_gib':round(min(s['disk_free_bytes'] for r in rows if r['label'] in set(success+failures) for s in r['samples'])/1024**3,2),
 'lsp_checks':lsps,'final_host':host_sample()}
(ROOT/'final-check.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
