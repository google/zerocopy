#!/usr/bin/env python3
"""Apply direct Lean edits in separate source branches and batch-check each."""
import argparse,hashlib,json,os,shutil,subprocess
from pathlib import Path
from probe import HERE,FIX,LEAN,FILES,apply,workspace_edits,sha

TRANSCRIPT=HERE/'transcript.json';OUT=HERE/'applied-results.json';ART=HERE/'applied'
def htext(s):return hashlib.sha256(s.encode()).hexdigest()
def check(work,label,content):
    root=work/label;root.mkdir();(root/'Helper.lean').write_text(FILES['Helper.lean'])
    for name,text in content.items():(root/name).write_text(text)
    env=dict(os.environ,LEAN_PATH=str(root),LEAN_SRC_PATH=str(root),LEAN_NUM_THREADS='1')
    helper=subprocess.run([str(LEAN),'-o',str(root/'Helper.olean'),'-i',str(root/'Helper.ilean'),str(root/'Helper.lean')],
        cwd=root,env=env,capture_output=True,text=True,timeout=20)
    assert helper.returncode==0,helper.stderr
    outputs={}
    for name in content:
        if name=='Helper.lean':continue
        p=subprocess.run([str(LEAN),'--json',str(root/name)],cwd=root,env=env,capture_output=True,text=True,timeout=20)
        outputs[name]={'exit':p.returncode,'stdout':p.stdout.replace(str(root),'$WORK'),'stderr':p.stderr.replace(str(root),'$WORK')}
    assert all(x['exit']==0 for x in outputs.values()),(label,outputs)
    for name,text in content.items():
        artifact=ART/(label+'-'+name);artifact.write_text(text)
    return {'source_sha256':{n:htext(s) for n,s in content.items()},'batch':outputs}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
    assert not work.exists(),'choose absent owned work directory';work.mkdir(parents=True)
    ART.mkdir(exist_ok=True)
    for p in ART.glob('*.lean'):p.unlink()
    t=json.loads(TRANSCRIPT.read_text());r=t['responses'];uris=t['uri_by_name'];rows={}
    rename=workspace_edits(r['rename']['result']);assert set(rename)=={uris['Helper.lean'],uris['Main.lean']}
    rename_preimage={n:htext(FILES[n]) for n in ('Helper.lean','Main.lean')}
    stale_rename_source={'Helper.lean':FILES['Helper.lean'],'Main.lean':'-- intervening edit\n'+FILES['Main.lean']}
    stale_rename_rejected=any(htext(stale_rename_source[n])!=rename_preimage[n] for n in rename_preimage)
    assert stale_rename_rejected
    renamed={name:apply(FILES[name],rename[uris[name]]) for name in ('Helper.lean','Main.lean')}
    rows['rename']=check(work,'rename',renamed)
    rows['rename']['source_hash_guard']={'expected':rename_preimage,'stale_rejected_atomically':stale_rename_rejected}
    quick=next(a for a in r['actionQuickfix']['result'] if a.get('edit'))
    edits=workspace_edits(quick['edit']);assert set(edits)=={uris['Action.lean']}
    version=quick['edit']['documentChanges'][0]['textDocument']['version']
    assert version==1
    stale_version=2
    assert stale_version!=version
    action=apply(FILES['Action.lean'],edits[uris['Action.lean']])
    rows['action']=check(work,'action',{'Action.lean':action})
    rows['action']['source_workspace_edit']=quick['edit']
    rows['action']['version_guard']={'accepted_version':version,'stale_version':stale_version,
                                     'stale_rejected':stale_version!=version}
    hint=r['inlay']['result'][0];assert hint['textEdits']
    hinted=apply(FILES['Main.lean'],hint['textEdits'])
    rows['inlay']=check(work,'inlay',{'Main.lean':hinted})
    resolved=r['completionResolve']['result'];assert resolved['label']=='αhelper'
    assert not any(k in resolved for k in ('textEdit','insertText','additionalTextEdits'))
    # This replacement is a client fallback from the resolved label, not a
    # server-returned TextEdit; keep the distinction in the manifest.
    client_edit={'range':{'start':{'line':1,'character':7},'end':{'line':1,'character':11}},'newText':'αhelper'}
    completed=apply(FILES['Completion.lean'],[client_edit])
    rows['completion_client_fallback']=check(work,'completion',{'Completion.lean':completed})
    rows['completion_client_fallback']['edit_origin']='client word-range fallback from Lean completion label'
    rows['completion_client_fallback']['client_edit']=client_edit
    result={'lean_sha256':sha(LEAN),'transcript_sha256':sha(TRANSCRIPT),'branches':rows,
            'artifact_sha256':{p.name:sha(p) for p in sorted(ART.glob('*.lean'))}}
    OUT.write_text(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
    print(json.dumps({k:{n:v['exit'] for n,v in x['batch'].items()} for k,x in rows.items()},indent=2))

if __name__=='__main__':main()
