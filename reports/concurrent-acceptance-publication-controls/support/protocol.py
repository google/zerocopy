#!/usr/bin/env python3
"""Controlled same-user processes; no sandbox or authenticated producer stages."""
import argparse, copy, fcntl, hashlib, json, os, signal, subprocess, sys, time, uuid
from pathlib import Path

def encoded(x): return json.dumps(x,sort_keys=True,separators=(',',':')).encode()
def digest(x): return hashlib.sha256(x).hexdigest()
def atomic(path, x):
    tmp=path.with_name(path.name+'.tmp-'+uuid.uuid4().hex)
    with open(tmp,'xb') as f: f.write(encoded(x));f.flush();os.fsync(f.fileno())
    os.replace(tmp,path)
    fd=os.open(path.parent,os.O_RDONLY);os.fsync(fd);os.close(fd)

def subject(epoch=1):
    return {'epoch':epoch,'program':'finite-add-one-v1','property':'table[i]=i+1',
            'domain':list(range(16)),'target':'nat-unbounded','callee':'add-one',
            'generic_instance':'Nat','associated_type':'Nat','dispatch':'direct',
            'required_effects':['guard','cleanup','dependency'],'required_stages':['capture','proof']}
def candidate(ch):
    return {'subject':copy.deepcopy(ch),'table':[i+1 for i in ch['domain']],'effects':list(ch['required_effects'])}
def semantic_check(ch, data):
    if type(data) is not dict or set(data)!={'subject','table','effects'}: return 'malformed'
    if type(data['table']) is not list or any(type(x) is not int or x < 0 for x in data['table']):return 'malformed'
    if type(data['subject']) is not dict:return 'malformed'
    if encoded(data['subject'])!=encoded(ch): return 'subject-mismatch'
    if data['effects']!=ch['required_effects']: return 'omitted-effect'
    if data['table']!=[i+1 for i in ch['domain']]: return 'semantic-mismatch'
    return 'checked'

def producer(args):
    root=Path(args.root).resolve();ch=json.loads((root/'input.json').read_text())
    if args.mode=='fail': sys.exit(7)
    if args.mode=='hang': time.sleep(60);return
    if args.mode=='challenge-write':
        altered=copy.deepcopy(ch);altered['property']='True';atomic(root.parent.parent/'challenge.json',altered);print('challenge write succeeded')
    if args.mode=='policy-write':
        atomic(root.parent.parent/'policy.json',{'allow':'everything'});print('policy write succeeded')
    if args.mode=='input-write':
        altered=copy.deepcopy(ch);altered['target']='wrong-target';atomic(root/'input.json',altered);print('checker input write succeeded')
    if args.mode=='final-write': atomic(root.parent.parent/'accepted.json',{'verdict':'accepted','subject':ch,'data':{'table':[0]*16}});print('final record write succeeded')
    d=candidate(ch)
    if args.mode=='bad-table':d['table'][7]=0
    if args.mode=='boolean-table':d['table'][0]=True
    if args.mode=='boolean-subject':d['subject']['epoch']=True
    if args.mode=='scalar-schema':d=42
    if args.mode=='malformed-json':
        (root/'candidate.json').write_bytes(b'{broken');return
    if args.mode=='omit-cleanup':d['effects'].remove('cleanup')
    if args.mode=='wrong-generic':d['subject']['generic_instance']='Int'
    if args.mode=='wrong-associated':d['subject']['associated_type']='Bool'
    if args.mode=='wrong-dispatch':d['subject']['dispatch']='vtable-foreign'
    if args.mode=='wrong-callee':d['subject']['callee']='zero'
    if args.mode=='partial-crash':
        (root/'candidate.partial').write_bytes(b'{"subject":');sys.exit(9)
    if args.delay: time.sleep(args.delay)
    atomic(root/'candidate.json',d)
    if args.mode=='missing-stage':return
    # Labels written by producer are deliberately ignored by admission.
    atomic(root/'producer-labels.json',{'capture':'complete','proof':'complete'})

def run_stage(run,mode,delay=0,timeout=2,cancel=False):
    cmd=[sys.executable,'-B',str(Path(__file__).resolve()),'produce','--root',str(run),'--mode',mode,'--delay',str(delay)]
    start=time.perf_counter();p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if cancel:
        time.sleep(.04);p.terminate()
    try: out,err=p.communicate(timeout=timeout);state='cancelled' if cancel else 'exited'
    except subprocess.TimeoutExpired:
        p.kill();out,err=p.communicate();state='timeout'
    r={'command':cmd,'pid':p.pid,'state':state,'returncode':p.returncode,
       'duration_ms':round((time.perf_counter()-start)*1000,3),'stdout':out.decode(),'stderr':err.decode()}
    atomic(run/'process.json',r);return r

def begin(root,ch,do_capture=True):
    run=root/'runs'/uuid.uuid4().hex;run.mkdir(parents=True);atomic(run/'input.json',ch)
    if do_capture:
        code="import hashlib,json,sys;from pathlib import Path;p=Path(sys.argv[1]);b=(p/'input.json').read_bytes();(p/'capture.json').write_text(json.dumps({'input_sha256':hashlib.sha256(b).hexdigest()}))"
        cap=subprocess.run([sys.executable,'-B','-c',code,str(run)],capture_output=True)
        atomic(run/'capture-process.json',{'returncode':cap.returncode,'stdout':cap.stdout.decode(),'stderr':cap.stderr.decode()})
    return run
def admit(root,run,ch,observed,missing_capture=False,crash_before_replace=False):
    if observed['state']!='exited' or observed['returncode']!=0:return 'producer-'+(str(observed['returncode']) if observed['state']=='exited' else observed['state'])
    if not (run/'capture.json').is_file() or not (run/'capture-process.json').is_file():return 'missing-consumer-stage'
    cap=json.loads((run/'capture-process.json').read_text());captured=json.loads((run/'capture.json').read_text())
    if cap['returncode']!=0 or captured['input_sha256']!=digest(encoded(ch)):return 'capture-failure'
    if (root/'policy.json').read_bytes()!=encoded({'mandatory':'table-and-binding-v1'}):return 'policy-changed'
    if (run/'input.json').read_bytes()!=encoded(ch):return 'checker-input-changed'
    path=run/'candidate.json'
    if not path.is_file():return 'missing-candidate'
    raw=path.read_bytes()
    try:data=json.loads(raw)
    except (ValueError,UnicodeError):return 'malformed'
    checked=semantic_check(ch,data)
    if checked!='checked':return checked
    with open(root/'commit.lock','a+b') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX)
        current=json.loads((root/'challenge.json').read_text())
        if encoded(current)!=encoded(ch):return 'stale-generation'
        final={'verdict':'accepted','subject':ch,'candidate_sha256':digest(raw),'data':data,
               'consumer_observed_process':{k:observed[k] for k in ['pid','state','returncode']}}
        if crash_before_replace:
            (root/'accepted.partial').write_bytes(encoded(final)[:37]);return 'consumer-partial-no-commit'
        atomic(root/'accepted.json',final);return 'accepted'

def read_accepted(root):
    try:
        final=json.loads((root/'accepted.json').read_text());ch=json.loads((root/'challenge.json').read_text())
        if set(final)!={'verdict','subject','candidate_sha256','data','consumer_observed_process'}:return 'record-malformed'
        if final['verdict']!='accepted' or encoded(final['subject'])!=encoded(ch):return 'record-stale'
        if semantic_check(ch,final['data'])!='checked':return 'record-semantics-rejected'
        if digest(encoded(final['data']))!=final['candidate_sha256']:return 'record-data-binding-rejected'
        return 'accepted-data-rechecked'
    except (FileNotFoundError,ValueError,KeyError,TypeError):return 'no-valid-record'

def experiment(base):
    base=base.resolve();base.mkdir(exist_ok=True);root=base/('run-'+uuid.uuid4().hex);root.mkdir();(root/'runs').mkdir()
    results=[]
    modes=['good','bad-table','boolean-table','boolean-subject','scalar-schema','malformed-json','omit-cleanup','wrong-generic','wrong-associated','wrong-dispatch','wrong-callee','fail','partial-crash','hang','challenge-write','policy-write','input-write','final-write']
    for mode in modes:
        ch=subject();atomic(root/'challenge.json',ch);atomic(root/'policy.json',{'mandatory':'table-and-binding-v1'})
        final=root/'accepted.json'
        if final.exists():final.unlink()
        run=begin(root,ch);obs=run_stage(run,mode,timeout=.12 if mode=='hang' else 2)
        before_admission=read_accepted(root)
        verdict=admit(root,run,ch,obs)
        results.append({'case':mode,'verdict':verdict,'pre_admission_readback':before_admission,'readback':read_accepted(root),'process':obs,'run':str(run.relative_to(root))})
    for mode in ['cancel','missing-consumer-stage','consumer-partial']:
        ch=subject();atomic(root/'challenge.json',ch);atomic(root/'policy.json',{'mandatory':'table-and-binding-v1'})
        if (root/'accepted.json').exists():(root/'accepted.json').unlink()
        run=begin(root,ch,do_capture=mode!='missing-consumer-stage');obs=run_stage(run,'hang' if mode=='cancel' else 'good',cancel=mode=='cancel')
        verdict=admit(root,run,ch,obs,missing_capture=mode=='missing-consumer-stage',crash_before_replace=mode=='consumer-partial')
        results.append({'case':mode,'verdict':verdict,'readback':read_accepted(root),'process':obs})
    # Actual overlapping subprocesses, independently selected epochs, old result
    # admitted only after the new one has been published.
    ch1=subject(1);ch2=subject(2);atomic(root/'challenge.json',ch1)
    r1=begin(root,ch1);r2=begin(root,ch2)
    cmd=lambda r,delay:[sys.executable,'-B',str(Path(__file__).resolve()),'produce','--root',str(r),'--mode','good','--delay',str(delay)]
    p1=subprocess.Popen(cmd(r1,.25),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    atomic(root/'challenge.json',ch2)
    p2=subprocess.Popen(cmd(r2,0),stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    out2,err2=p2.communicate(timeout=2);o2={'pid':p2.pid,'state':'exited','returncode':p2.returncode}
    v2=admit(root,r2,ch2,o2)
    out1,err1=p1.communicate(timeout=2);o1={'pid':p1.pid,'state':'exited','returncode':p1.returncode}
    v1=admit(root,r1,ch1,o1)
    atomic(r1/'process.json',o1);atomic(r2/'process.json',o2)
    commits=[]
    for r in [r1,r2]:
        proc=subprocess.Popen([sys.executable,'-B',str(Path(__file__).resolve()),'admit','--root',str(root),'--run',str(r)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        commits.append(proc)
    commit_results=[]
    for proc in commits:
        out,err=proc.communicate(timeout=2);commit_results.append({'pid':proc.pid,'returncode':proc.returncode,'stdout':out.decode(),'stderr':err.decode()})
    results.append({'case':'parallel-consumers','consumers':commit_results,'readback':read_accepted(root)})
    results.append({'case':'overlapping-generations','new':v2,'old':v1,'readback':read_accepted(root),'pids':[p1.pid,p2.pid],'returncodes':[p1.returncode,p2.returncode],'stdout':[out1.decode(),out2.decode()],'stderr':[err1.decode(),err2.decode()]})
    # A real consumer process dies after a partial write; committed record remains.
    prior=(root/'accepted.json').read_bytes()
    crash=subprocess.run([sys.executable,'-B','-c',"import os,sys;open(sys.argv[1],'wb').write(b'{partial');os._exit(13)",str(root/'accepted.partial')],capture_output=True)
    results.append({'case':'consumer-crash-before-replace','returncode':crash.returncode,'prior_record_unchanged':(root/'accepted.json').read_bytes()==prior,'readback':read_accepted(root)})
    # Same-user threat countercontrol: final file can really be overwritten.
    final=json.loads(prior);final['data']['table'][3]=0;atomic(root/'accepted.json',final)
    results.append({'case':'postcommit-same-user-tamper','write_succeeded':True,'readback':read_accepted(root)})
    atomic(root/'results.json',results)
    return {'run_root':str(root),'cases':results,'threat_boundary':'Same-user ordinary subprocesses; no OS producer isolation, durable tamper-proof journal, verified filesystem, or authenticated producer-reported stage coverage.'}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('role',choices=['produce','experiment','admit']);ap.add_argument('--root',required=True);ap.add_argument('--run');ap.add_argument('--mode',default='good');ap.add_argument('--delay',type=float,default=0);args=ap.parse_args()
    if args.role=='produce':producer(args)
    elif args.role=='admit':
        r=Path(args.run);ch=json.loads((r/'input.json').read_text());obs=json.loads((r/'process.json').read_text())
        print(admit(Path(args.root),r,ch,obs))
    else:print(json.dumps(experiment(Path(args.root)),indent=2))
