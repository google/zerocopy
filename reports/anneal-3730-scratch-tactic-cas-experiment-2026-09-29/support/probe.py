#!/usr/bin/env python3
"""Prototype scratch Lean candidate checks and exact-preimage generation CAS."""
import argparse,fcntl,hashlib,json,os,shutil,signal,subprocess,time
from pathlib import Path

HERE=Path(__file__).resolve().parent
LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
OUT=HERE/'results.json';ART=HERE/'artifacts'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def write_json(path,data):path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
def atomic_json(path,data):
    tmp=path.with_suffix('.tmp');write_json(tmp,data);os.replace(tmp,path)
def env_for(root):return dict(os.environ,LEAN_PATH=str(root),LEAN_NUM_THREADS='1')
def theorem_header(text):
    # Fixture-specific check: the single theorem's binder/target line must
    # remain byte-identical. This is not a general Lean proposition oracle.
    return next(line for line in text.splitlines() if line.startswith('theorem demo '))
def compile_env(root):
    r=subprocess.run([str(LEAN),'-o',str(root/'ProbeEnv.olean'),str(root/'ProbeEnv.lean')],
                     cwd=root,env=env_for(root),capture_output=True,text=True,timeout=20)
    assert r.returncode==0,r.stderr
    return sha(root/'ProbeEnv.olean')
def snapshot(work):
    ptr=json.loads((work/'CURRENT.json').read_text())
    gen=work/'generations'/ptr['generation']
    assert sha(gen/'Proof.lean')==ptr['source_sha256']
    assert sha(gen/'ProbeEnv.lean')==ptr['env_source_sha256']
    assert sha(gen/'ProbeEnv.olean')==ptr['env_olean_sha256']
    return ptr,gen
def create_generation(work,number,proof,env_text,request):
    name=f'g{number:04d}';root=work/'generations'/name;root.mkdir()
    (root/'Proof.lean').write_text(proof);(root/'ProbeEnv.lean').write_text(env_text)
    olean=compile_env(root)
    return {'version':number,'generation':name,'source_sha256':sha(root/'Proof.lean'),
            'env_source_sha256':sha(root/'ProbeEnv.lean'),'env_olean_sha256':olean,
            'lean_sha256':sha(LEAN),'accepted_request':request}
def make_candidate(work,label,base,base_dir,proof,existing=None):
    root=existing or work/'scratch'/label
    if root.exists():shutil.rmtree(root)
    root.mkdir(parents=True)
    for name in ('ProbeEnv.lean','ProbeEnv.olean'):shutil.copyfile(base_dir/name,root/name)
    (root/'Proof.lean').write_text(proof)
    c={'request':label,'root':root,'base':dict(base),'source_sha256':sha(root/'Proof.lean'),
       'environment_sha256':sha(root/'ProbeEnv.lean'),'olean_sha256':sha(root/'ProbeEnv.olean'),
       'lean_sha256':sha(LEAN),'statement_sha256':hashlib.sha256(theorem_header(proof).encode()).hexdigest(),
       'status':'unchecked'}
    return c
def batch(candidate,cancel=False):
    root=candidate['root'];cmd=[str(LEAN),'--json',str(root/'Proof.lean')]
    if cancel:
        p=subprocess.Popen(cmd,cwd=root,env=env_for(root),stdout=subprocess.PIPE,stderr=subprocess.PIPE,
                           text=True,start_new_session=True)
        os.killpg(p.pid,signal.SIGSTOP);os.killpg(p.pid,signal.SIGKILL)
        stdout,stderr=p.communicate(timeout=5)
        candidate['batch']={'exit':p.returncode,'stdout':stdout,'stderr':stderr,'cancelled':True,
                            'remaining_group':False}
        try:os.killpg(p.pid,0);candidate['batch']['remaining_group']=True
        except ProcessLookupError:pass
        assert p.returncode==-9 and not candidate['batch']['remaining_group']
        candidate['status']='cancelled';return candidate
    r=subprocess.run(cmd,cwd=root,env=env_for(root),capture_output=True,text=True,timeout=20)
    candidate['batch']={'exit':r.returncode,'stdout':r.stdout.replace(str(root),'$SCRATCH'),
                        'stderr':r.stderr.replace(str(root),'$SCRATCH'),'cancelled':False}
    text=(root/'Proof.lean').read_text()
    baseline_statement=hashlib.sha256(theorem_header((HERE/'fixture/Proof.lean').read_text()).encode()).hexdigest()
    if r.returncode==0 and candidate['statement_sha256']!=baseline_statement:
        candidate['status']='invalid_context'
    else:
        candidate['status']='valid' if r.returncode==0 and 'sorry' not in text and 'admit' not in text else 'invalid'
    return candidate
def apply_candidate(work,candidate,journal):
    with (work/'LOCK').open('a+') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        current,current_dir=snapshot(work)
        req=candidate['request']
        if req in journal:return {'result':'duplicate','request':req,'version':journal[req],
                                  'pointer_sha256':sha(work/'CURRENT.json')}
        def reject(reason):return {'result':'rejected','reason':reason,'request':req,
                                   'version':current['version'],'pointer_sha256':sha(work/'CURRENT.json')}
        if candidate['status']!='valid':return reject(candidate['status'])
        if sha(candidate['root']/'Proof.lean')!=candidate['source_sha256']:return reject('candidate_source_changed')
        if hashlib.sha256(theorem_header((candidate['root']/'Proof.lean').read_text()).encode()).hexdigest()!=candidate['statement_sha256']:
            return reject('candidate_statement_changed')
        if sha(candidate['root']/'ProbeEnv.lean')!=candidate['environment_sha256'] or sha(candidate['root']/'ProbeEnv.olean')!=candidate['olean_sha256']:
            return reject('candidate_environment_changed')
        if candidate['lean_sha256']!=sha(LEAN):return reject('tool_changed')
        base=candidate['base']
        if base['env_source_sha256']!=current['env_source_sha256'] or base['env_olean_sha256']!=current['env_olean_sha256']:
            return reject('environment_changed')
        if base['source_sha256']!=current['source_sha256']:return reject('stale_source')
        if base['version']!=current['version']:return reject('stale_version')
        if candidate['environment_sha256']!=current['env_source_sha256'] or candidate['olean_sha256']!=current['env_olean_sha256']:
            return reject('candidate_environment_not_current')
        nextptr=create_generation(work,current['version']+1,(candidate['root']/'Proof.lean').read_text(),
                                  (current_dir/'ProbeEnv.lean').read_text(),req)
        atomic_json(work/'CURRENT.json',nextptr)
        journal[req]=nextptr['version'];write_json(work/'JOURNAL.json',journal)
        return {'result':'accepted','request':req,'version':nextptr['version'],
                'pointer_sha256':sha(work/'CURRENT.json')}
def summarize(c):
    return {'request':c['request'],'base_version':c['base']['version'],'base_source_sha256':c['base']['source_sha256'],
            'base_env_sha256':c['base']['env_source_sha256'],'candidate_sha256':c['source_sha256'],
            'status':c['status'],'batch':c.get('batch')}
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
    assert not work.exists(),'choose absent owned work path'
    assert shutil.disk_usage(work.parent).free>=15*(1<<30),'15 GiB free-disk guard'
    (work/'generations').mkdir(parents=True);(work/'scratch').mkdir();ART.mkdir(exist_ok=True)
    proof=(HERE/'fixture/Proof.lean').read_text();env_text=(HERE/'fixture/ProbeEnv.lean').read_text()
    first=create_generation(work,1,proof,env_text,'bootstrap');atomic_json(work/'CURRENT.json',first)
    journal={};write_json(work/'JOURNAL.json',journal);events=[];candidates=[]
    def record(label,c,decision):
        current,_=snapshot(work)
        events.append({'label':label,'candidate':summarize(c),'decision':decision,'current':current})
        candidates.append(c)
    base,root=snapshot(work)
    good=make_candidate(work,'good-A',base,root,proof.replace('exact Nat.add_zero n','simp'));batch(good)
    decision=apply_candidate(work,good,journal);record('accept',good,decision);assert decision['result']=='accepted'
    dup=apply_candidate(work,good,journal);record('duplicate_retry',good,dup);assert dup['result']=='duplicate'
    stale=make_candidate(work,'stale-source',base,root,proof);batch(stale)
    decision=apply_candidate(work,stale,journal);record('stale_source',stale,decision);assert decision['reason']=='stale_source'
    base2,root2=snapshot(work)
    partial=make_candidate(work,'partial',base2,root2,(root2/'Proof.lean').read_text().replace('simp','skip'));batch(partial)
    decision=apply_candidate(work,partial,journal);record('partial_tactic',partial,decision);assert decision['reason']=='invalid'
    failed=make_candidate(work,'failed',base2,root2,(root2/'Proof.lean').read_text().replace('simp','exact False.elim'));batch(failed)
    decision=apply_candidate(work,failed,journal);record('failed_tactic',failed,decision);assert decision['reason']=='invalid'
    sorry=make_candidate(work,'sorry',base2,root2,(root2/'Proof.lean').read_text().replace('simp','sorry'));batch(sorry)
    decision=apply_candidate(work,sorry,journal);record('sorry_tactic',sorry,decision)
    assert sorry['batch']['exit']==0 and decision['reason']=='invalid'
    vacuous_source=(root2/'Proof.lean').read_text().replace('n + 0 = n','n = n').replace('simp','rfl')
    vacuous=make_candidate(work,'statement-changed',base2,root2,vacuous_source);batch(vacuous)
    decision=apply_candidate(work,vacuous,journal);record('statement_changed',vacuous,decision)
    assert vacuous['batch']['exit']==0 and decision['reason']=='invalid_context'
    mutated=make_candidate(work,'mutated',base2,root2,(root2/'Proof.lean').read_text().replace('simp','exact Nat.add_zero n'));batch(mutated)
    (mutated['root']/'Proof.lean').write_text((mutated['root']/'Proof.lean').read_text()+'-- after check\n')
    decision=apply_candidate(work,mutated,journal);record('candidate_mutated',mutated,decision);assert decision['reason']=='candidate_source_changed'
    env_old=make_candidate(work,'old-environment',base2,root2,(root2/'Proof.lean').read_text().replace('simp','exact Nat.add_zero n'));batch(env_old)
    # Explicit simulated canonical environment revision; proof bytes remain fixed.
    current,current_dir=snapshot(work)
    newenv=(current_dir/'ProbeEnv.lean').read_text().replace(':= 7',':= 8')
    assert newenv!=(current_dir/'ProbeEnv.lean').read_text()
    nextptr=create_generation(work,current['version']+1,(current_dir/'Proof.lean').read_text(),newenv,'environment-update')
    atomic_json(work/'CURRENT.json',nextptr)
    decision=apply_candidate(work,env_old,journal);record('environment_changed',env_old,decision);assert decision['reason']=='environment_changed'
    base3,root3=snapshot(work)
    canceled=make_candidate(work,'cancel-and-reuse',base3,root3,(root3/'Proof.lean').read_text().replace('simp','exact Nat.add_zero n'))
    batch(canceled,cancel=True)
    decision=apply_candidate(work,canceled,journal);record('cancelled',canceled,decision);assert decision['reason']=='cancelled'
    reuse=make_candidate(work,'reuse-after-cancel',base3,root3,(root3/'Proof.lean').read_text().replace('simp','exact Nat.add_zero n'),existing=canceled['root'])
    batch(reuse);decision=apply_candidate(work,reuse,journal);record('reuse_accept',reuse,decision);assert decision['result']=='accepted'
    final,final_dir=snapshot(work);assert final['version']==4 and final['source_sha256']==sha(final_dir/'Proof.lean')
    final_run=subprocess.run([str(LEAN),'--json',str(final_dir/'Proof.lean')],cwd=final_dir,env=env_for(final_dir),
                             capture_output=True,text=True,timeout=20)
    assert final_run.returncode==0
    assert final_run.stdout==reuse['batch']['stdout'] and final_run.stderr==reuse['batch']['stderr']
    for name,path in {'initial-Proof.lean':work/'generations/g0001/Proof.lean',
                      'accepted-Proof.lean':work/'generations/g0002/Proof.lean',
                      'final-Proof.lean':final_dir/'Proof.lean',
                      'final-ProbeEnv.lean':final_dir/'ProbeEnv.lean'}.items():shutil.copyfile(path,ART/name)
    result={'prototype_only':True,'lean_sha256':sha(LEAN),'fixture_sha256':{'proof':sha(HERE/'fixture/Proof.lean'),
            'environment':sha(HERE/'fixture/ProbeEnv.lean')},'initial':first,'events':events,'final':final,
            'artifact_sha256':{p.name:sha(p) for p in ART.glob('*.lean')},
            'final_batch':{'exit':final_run.returncode,'stdout':final_run.stdout,'stderr':final_run.stderr,
                           'matches_reuse_candidate_batch':True},
            'canonical_generation_count':len(list((work/'generations').iterdir())),
            'journal':journal}
    write_json(OUT,result)
    print(json.dumps([{'label':e['label'],'result':e['decision']['result'],
                       'reason':e['decision'].get('reason'),'version':e['current']['version']} for e in events],indent=2))

if __name__=='__main__':main()
