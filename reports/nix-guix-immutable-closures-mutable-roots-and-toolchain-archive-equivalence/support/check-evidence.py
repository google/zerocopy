#!/usr/bin/env python3
import argparse,json,sys
p=argparse.ArgumentParser();p.add_argument('--query',required=True);p.add_argument('--concurrency',required=True);a=p.parse_args()
q=json.load(open(a.query));c=json.load(open(a.concurrency))
obs={e['data']['label']:e['data'].get('result') for e in q if e['kind']=='goal_observation'}
errors=[d['message'] for e in q if e['kind']=='server' and e['data'].get('method')=='textDocument/publishDiagnostics' for d in e['data'].get('params',{}).get('diagnostics',[]) if d.get('severity')==1]
checks={
 'pre_edit_apply_has_one_goal':bool(obs.get('initial-before-tactic',{}).get('goals')) and len(obs.get('initial-before-tactic',{}).get('goals',[]))==1,
 'post_apply_has_two_goals':len(obs.get('initial-after-tactic',{}).get('goals',[]))==2,
 'baseline_rfl_has_no_goals':obs.get('edited-v2-after-tactic',{}).get('rendered')=='no goals',
 'same_server_still_reports_no_goals_after_dependency_change':obs.get('same-server-after-dependency-rebuild-after-tactic',{}).get('rendered')=='no goals',
 'fresh_server_reports_open_goal_after_dependency_change':bool(obs.get('fresh-after-change-after-tactic',{}).get('goals')),
 'fresh_server_reports_dependency_mismatch':any('rfl' in x and ('expected' in x or 'not definitionally equal' in x) for x in errors),
}
cs=[e for e in c if e['kind']=='resource_sample'];two=[e for e in cs if e.get('active_servers')==2]
checks['two_server_sample_present']=bool(two)
checks['rss_below_3_5_gib']=bool(two) and max(e['aggregate_tree_rss_bytes'] for e in two)<3_500_000_000
checks['memory_floor_at_least_20_percent']=bool(cs) and all((e.get('memory_free_percent') is None or e['memory_free_percent']>=20) for e in cs)
checks['servers_stopped']=any(e.get('active_servers')==0 for e in cs)
print(json.dumps(checks,indent=2,sort_keys=True))
sys.exit(0 if all(checks.values()) else 1)
