#!/usr/bin/env python3
"""Two-client Lean candidate CAS and process-crash publication controls."""
import argparse,fcntl,hashlib,json,multiprocessing as mp,os,shutil,subprocess,time,uuid
from pathlib import Path

HERE=Path(__file__).resolve().parent;LEAN=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean')
OUT=HERE/'results.json';ART=HERE/'artifacts'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def jbytes(v):return (json.dumps(v,indent=2,sort_keys=True)+'\n').encode()
def write(path,v):Path(path).write_bytes(jbytes(v))
def atomic_write(path,v):
    tmp=Path(str(path)+'.tmp');tmp.write_bytes(jbytes(v));os.replace(tmp,path)
def env(root):return dict(os.environ,LEAN_PATH=str(root),LEAN_NUM_THREADS='1')
def run_lean(root,file,output=None):
    cmd=[str(LEAN)]
    if output:cmd+=['-o',str(output)]
    else:cmd+=['--json']
    cmd.append(str(root/file))
    p=subprocess.run(cmd,cwd=root,env=env(root),capture_output=True,text=True,timeout=20)
    return {'exit':p.returncode,'stdout':p.stdout.replace(str(root),'$ROOT'),
            'stderr':p.stderr.replace(str(root),'$ROOT')}
def complete_generation(work,name,version,proof,env_source,request):
    root=work/'generations'/name;root.mkdir()
    (root/'Proof.lean').write_text(proof);(root/'ProbeEnv.lean').write_text(env_source)
    check=run_lean(root,'ProbeEnv.lean',root/'ProbeEnv.olean');assert check['exit']==0,check
    manifest={'complete':True,'generation':name,'version':version,'request':request,
              'proof_sha256':sha(root/'Proof.lean'),'env_sha256':sha(root/'ProbeEnv.lean'),
              'olean_sha256':sha(root/'ProbeEnv.olean'),'lean_sha256':sha(LEAN)}
    write(root/'MANIFEST.json',manifest)
    return manifest
def current(work):
    ptr=json.loads((work/'CURRENT.json').read_text());root=work/'generations'/ptr['generation']
    man=json.loads((root/'MANIFEST.json').read_text())
    assert man==ptr and man['complete'] and man['lean_sha256']==sha(LEAN)
    assert sha(root/'Proof.lean')==man['proof_sha256']
    assert sha(root/'ProbeEnv.lean')==man['env_sha256']
    assert sha(root/'ProbeEnv.olean')==man['olean_sha256']
    return ptr,root
def candidate(work,label,base,base_root,proof):
    root=work/'scratch'/label;root.mkdir()
    (root/'Proof.lean').write_text(proof)
    for n in ('ProbeEnv.lean','ProbeEnv.olean'):shutil.copyfile(base_root/n,root/n)
    result=run_lean(root,'Proof.lean')
    return {'label':label,'root':str(root),'base':base,'source_sha256':sha(root/'Proof.lean'),
            'env_sha256':sha(root/'ProbeEnv.lean'),'olean_sha256':sha(root/'ProbeEnv.olean'),
            'batch':result}
def apply(work,c,crash=None,marker=None):
    with (work/'LOCK').open('a+') as f:
        fcntl.flock(f,fcntl.LOCK_EX)
        ptr,root=current(work);cand=Path(c['root'])
        def reject(reason):return {'result':'rejected','reason':reason,'observed_version':ptr['version'],
                                   'pointer_sha256':sha(work/'CURRENT.json')}
        if c['batch']['exit']!=0:return reject('batch_failure')
        if sha(cand/'Proof.lean')!=c['source_sha256']:return reject('candidate_proof_mutated')
        if sha(cand/'ProbeEnv.lean')!=c['env_sha256'] or sha(cand/'ProbeEnv.olean')!=c['olean_sha256']:
            return reject('candidate_import_mutated')
        if 'sorry' in (cand/'Proof.lean').read_text():return reject('admission')
        if c['base']['proof_sha256']!=ptr['proof_sha256']:return reject('stale_proof')
        if c['base']['env_sha256']!=ptr['env_sha256'] or c['base']['olean_sha256']!=ptr['olean_sha256']:
            return reject('stale_environment')
        if c['base']['version']!=ptr['version']:return reject('stale_version')
        if c['env_sha256']!=ptr['env_sha256'] or c['olean_sha256']!=ptr['olean_sha256']:
            return reject('wrong_import')
        name=f"g{ptr['version']+1:04d}-{c['label']}-{uuid.uuid4().hex[:8]}"
        new=complete_generation(work,name,ptr['version']+1,(cand/'Proof.lean').read_text(),
                                (root/'ProbeEnv.lean').read_text(),c['label'])
        if crash=='pre_swap':
            write(marker,{'phase':crash,'created_generation':name,'current_before':ptr['generation']})
            os._exit(73)
        atomic_write(work/'CURRENT.json',new)
        if crash=='post_swap':
            write(marker,{'phase':crash,'created_generation':name,'current_before':ptr['generation']})
            os._exit(74)
        return {'result':'accepted','version':new['version'],'generation':name,
                'pointer_sha256':sha(work/'CURRENT.json')}
def competing_worker(work,label,base,base_root,proof,barrier,queue):
    c=candidate(work,label,base,base_root,proof)
    queue.put({'client':label,'event':'checked','pid':os.getpid(),'batch_exit':c['batch']['exit'],
               'candidate_sha256':c['source_sha256']})
    barrier.wait(timeout=10)
    decision=apply(work,c)
    queue.put({'client':label,'event':'applied','pid':os.getpid(),'decision':decision})
def crash_worker(work,label,base,base_root,proof,phase,marker):
    root=work/'scratch'/label;root.mkdir()
    (root/'Proof.lean').write_text(proof)
    for n in ('ProbeEnv.lean','ProbeEnv.olean'):shutil.copyfile(base_root/n,root/n)
    if phase=='materialized':
        write(marker,{'phase':phase,'candidate_sha256':sha(root/'Proof.lean')});os._exit(71)
    c={'label':label,'root':str(root),'base':base,'source_sha256':sha(root/'Proof.lean'),
       'env_sha256':sha(root/'ProbeEnv.lean'),'olean_sha256':sha(root/'ProbeEnv.olean'),
       'batch':run_lean(root,'Proof.lean')}
    assert c['batch']['exit']==0
    if phase=='checked':
        write(marker,{'phase':phase,'candidate_sha256':c['source_sha256'],'batch_exit':0});os._exit(72)
    apply(work,c,crash=phase,marker=marker)
    raise AssertionError('crash phase was not reached')
def read_old(root,ready,release,queue):
    with (root/'Proof.lean').open('rb') as f:
        ready.set();assert release.wait(10)
        queue.put({'pid':os.getpid(),'sha256':hashlib.sha256(f.read()).hexdigest(),
                   'path_exists':(root/'Proof.lean').exists()})
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);args=ap.parse_args();work=args.work.resolve()
    assert not work.exists(),'choose absent owned work path'
    assert shutil.disk_usage(work.parent).free>=15*(1<<30),'15 GiB free-disk guard'
    (work/'generations').mkdir(parents=True);(work/'scratch').mkdir();ART.mkdir(exist_ok=True)
    proof=(HERE/'fixture/Proof.lean').read_text();env_source=(HERE/'fixture/ProbeEnv.lean').read_text()
    initial=complete_generation(work,'g0001',1,proof,env_source,'bootstrap');atomic_write(work/'CURRENT.json',initial)
    ctx=mp.get_context('fork');barrier=ctx.Barrier(3);queue=ctx.Queue();base,base_root=current(work)
    variants=[proof.replace('exact Nat.add_zero n','simp'),proof.replace('exact Nat.add_zero n','simpa using Nat.add_zero n')]
    workers=[ctx.Process(target=competing_worker,args=(work,f'client-{i+1}',base,base_root,variants[i],barrier,queue)) for i in range(2)]
    for p in workers:p.start()
    checked=[queue.get(timeout=20) for _ in workers];assert all(x['event']=='checked' and x['batch_exit']==0 for x in checked)
    barrier.wait(timeout=10)
    for p in workers:p.join(timeout=20);assert p.exitcode==0
    applied=[queue.get(timeout=5) for _ in workers]
    assert sorted(x['decision']['result'] for x in applied)==['accepted','rejected']
    winner=next(x for x in applied if x['decision']['result']=='accepted')
    loser=next(x for x in applied if x['decision']['result']=='rejected')
    assert loser['decision']['reason']=='stale_proof'
    after_compete,_=current(work);assert after_compete['version']==2
    crashes=[]
    for phase,code in [('materialized',71),('checked',72),('pre_swap',73),('post_swap',74)]:
        before,before_root=current(work)
        replacement='exact Nat.add_zero n' if 'simp' in (before_root/'Proof.lean').read_text() else 'simp'
        candidate_proof=proof.replace('exact Nat.add_zero n',replacement)
        if candidate_proof==(before_root/'Proof.lean').read_text():candidate_proof=proof.replace('exact Nat.add_zero n','simpa using Nat.add_zero n')
        marker=work/f'{phase}.marker.json';p=ctx.Process(target=crash_worker,args=(work,f'crash-{phase}',before,before_root,candidate_proof,phase,marker))
        p.start();p.join(timeout=20);assert p.exitcode==code,(phase,p.exitcode)
        assert marker.exists();mark=json.loads(marker.read_text())
        recovered,recovered_root=current(work)
        fresh=run_lean(recovered_root,'Proof.lean');assert fresh['exit']==0
        expected_version=before['version']+(1 if phase=='post_swap' else 0)
        assert recovered['version']==expected_version
        crashes.append({'phase':phase,'exit':p.exitcode,'marker':mark,'before_version':before['version'],
                        'recovered_version':recovered['version'],'recovered_generation':recovered['generation'],
                        'fresh_batch':fresh,'pointer_sha256':sha(work/'CURRENT.json')})
    ptr,root=current(work)
    altered=proof.replace('exact Nat.add_zero n','simp')
    if altered==(root/'Proof.lean').read_text():altered=proof.replace('exact Nat.add_zero n','exact Nat.add_zero n\n  ') # harmless whitespace variant
    proof_mut=candidate(work,'mutate-proof',ptr,root,altered);assert proof_mut['batch']['exit']==0
    (Path(proof_mut['root'])/'Proof.lean').write_text((Path(proof_mut['root'])/'Proof.lean').read_text()+'-- changed after check\n')
    proof_reject=apply(work,proof_mut);assert proof_reject['reason']=='candidate_proof_mutated'
    import_mut=candidate(work,'mutate-import',ptr,root,altered);assert import_mut['batch']['exit']==0
    (Path(import_mut['root'])/'ProbeEnv.lean').write_text('def environmentValue : Nat := 99\n')
    import_reject=apply(work,import_mut);assert import_reject['reason']=='candidate_import_mutated'
    # Pin an old generation with a live reader while another valid proposal
    # switches CURRENT. The old directory is intentionally retained.
    pinned,pinned_root=current(work);ready=ctx.Event();release=ctx.Event();readerq=ctx.Queue()
    reader=ctx.Process(target=read_old,args=(pinned_root,ready,release,readerq));reader.start();assert ready.wait(10)
    live=candidate(work,'reader-swap',pinned,pinned_root,altered);assert live['batch']['exit']==0
    publish=apply(work,live);assert publish['result']=='accepted'
    release.set();reader.join(timeout=10);assert reader.exitcode==0
    observed=readerq.get(timeout=5);assert observed['sha256']==pinned['proof_sha256'] and observed['path_exists']
    final,final_root=current(work);final_batch=run_lean(final_root,'Proof.lean');assert final_batch['exit']==0
    assert final['version']==pinned['version']+1
    for name,path in {'initial-Proof.lean':work/'generations/g0001/Proof.lean',
                      'final-Proof.lean':final_root/'Proof.lean','final-ProbeEnv.lean':final_root/'ProbeEnv.lean'}.items():shutil.copyfile(path,ART/name)
    orphan_name=next(x for x in crashes if x['phase']=='pre_swap')['marker']['created_generation']
    shutil.copyfile(work/'generations'/orphan_name/'MANIFEST.json',ART/'orphan-MANIFEST.json')
    shutil.copyfile(final_root/'MANIFEST.json',ART/'final-MANIFEST.json')
    result={'prototype_only':True,'lean_sha256':sha(LEAN),'fixture_sha256':{'proof':sha(HERE/'fixture/Proof.lean'),
            'environment':sha(HERE/'fixture/ProbeEnv.lean')},'initial':initial,
            'competition':{'checked':checked,'applied':applied,'winner':winner['client'],'loser':loser['client'],
                           'after_version':after_compete['version']},
            'crashes':crashes,'mutation_controls':{'proof':{'decision':proof_reject,'batch_exit':proof_mut['batch']['exit']},
                                                  'import':{'decision':import_reject,'batch_exit':import_mut['batch']['exit']}},
            'reader':{'pinned_version':pinned['version'],'pinned_sha256':pinned['proof_sha256'],
                      'observed':observed,'publish':publish},
            'final':final,'final_batch':final_batch,
            'artifact_sha256':{p.name:sha(p) for p in ART.iterdir() if p.is_file()},
            'generation_count':len(list((work/'generations').iterdir()))}
    write(OUT,result)
    print(json.dumps({'competition':[(x['client'],x['decision']) for x in applied],
                      'crashes':[(x['phase'],x['exit'],x['recovered_version']) for x in crashes],
                      'mutation_reasons':[proof_reject['reason'],import_reject['reason']],
                      'reader':observed,'final_version':final['version'],'generation_count':result['generation_count']},indent=2))
if __name__=='__main__':main()
