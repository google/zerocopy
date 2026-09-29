#!/usr/bin/env python3
"""I086 one-shot Aeneas CLI file handoff vs Python byte-buffer wrapper."""
import hashlib,json,os,shutil,signal,statistics,subprocess,threading,time,tracemalloc
from pathlib import Path

HERE=Path(__file__).resolve().parent;WORK=HERE/'work'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
CHARON=TOOLS/'bin/charon';AENEAS=TOOLS/'bin/aeneas'
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
LEANROOT=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2';LEAN=LEANROOT/'bin/lean'
BACKEND=TOOLS/'aeneas-release/backends/lean'
PACKAGES=['Cli','batteries','Qq','aesop','proofwidgets','importGraph','LeanSearchClient','plausible','mathlib']
FLAGS=['-backend','lean','-no-progress-bar','-sequential','-split-files','-gen-lib-entry']
SOURCE='#![allow(dead_code)]\npub fn inc(x: u32) -> u32 { x.wrapping_add(1) }\n'
CHECK='import Source\nexample : handoff_probe.inc 0#u32 = .ok 1#u32 := by rfl\n'
COMMANDS=[]
def write(p,data):p=Path(p);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data if isinstance(data,bytes) else data.encode())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def inv(root):return {p.relative_to(root).as_posix():{'sha256':sha(p),'bytes':p.stat().st_size}
  for p in sorted(root.rglob('*')) if p.is_file() and not p.is_fifo()}
def rustenv():
    e=dict(os.environ);e.update(RUSTUP_HOME=str(TOOLS/'rustup'),CARGO_HOME=str(TOOLS/'cargo'),
      CHARON_TOOLCHAIN_IS_IN_PATH='1',CARGO_BUILD_JOBS='1',CARGO_INCREMENTAL='0',
      PATH=os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),e.get('PATH','')]))
    return e
def leanenv(comp):
    libs=[BACKEND/'.lake/packages'/p/'.lake/build/lib/lean' for p in PACKAGES]
    libs += [BACKEND/'.lake/build/lib/lean',LEANROOT/'lib/lean']
    e=dict(os.environ);e['LEAN_NUM_THREADS']='1';e['LEAN_PATH']=os.pathsep.join(str(p) for p in [comp,*libs] if p.is_dir())
    return e
def rss_sampler(pid,stop,samples):
    while not stop.is_set():
        p=subprocess.run(['ps','-o','rss=','-p',str(pid)],capture_output=True,text=True)
        try:samples.append(int(p.stdout.strip()))
        except ValueError:pass
        stop.wait(.025)
def run(label,args,cwd,env=None,input_bytes=None,timeout=90):
    argv=list(map(str,args));t=time.monotonic();p=subprocess.Popen(argv,cwd=cwd,env=env,
       stdin=subprocess.PIPE if input_bytes is not None else subprocess.DEVNULL,
       stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    stop=threading.Event();samples=[];thread=threading.Thread(target=rss_sampler,args=(p.pid,stop,samples),daemon=True);thread.start()
    try:out,err=p.communicate(input=input_bytes,timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid,signal.SIGKILL);out,err=p.communicate(timeout=5)
    stop.set();thread.join(timeout=2)
    row={'label':label,'argv':argv,'cwd':str(cwd),'pid':p.pid,'rc':p.returncode,
      'elapsed_ms':round((time.monotonic()-t)*1000,2),'peak_sampled_rss_kib':max(samples) if samples else None,
      'rss_sample_count':len(samples),'input_sha256':hashlib.sha256(input_bytes).hexdigest() if input_bytes is not None else None,
      'input_bytes':len(input_bytes) if input_bytes is not None else None,
      'stdout':out.decode(errors='replace'),'stderr':err.decode(errors='replace')}
    COMMANDS.append(row);return row
def aeneas_cmd(llbc,dest):return [AENEAS,*FLAGS,'-dest',dest,llbc]
def compile_files(label,generated):
    c=WORK/f'lean-{label}';(c/'Source').mkdir(parents=True)
    for m in ('Types','Funs'):shutil.copyfile(generated/f'{m}.lean',c/'Source'/f'{m}.lean')
    shutil.copyfile(generated/'Source.lean',c/'Source.lean')
    write(c/'Check.lean',CHECK);e=leanenv(c);chain=[]
    for m in ('Source/Types','Source/Funs','Source'):
        row=run(label+':lean:'+m,[LEAN,'-o',f'{m}.olean',f'{m}.lean'],c,e)
        chain.append(row);assert row['rc']==0,row
    check=run(label+':lean:oracle',[LEAN,'Check.lean'],c,e);assert check['rc']==0,check
    return {'chain_rc':[x['rc'] for x in chain],'oracle_rc':check['rc'],'oracle_stdout':check['stdout'],
      'compiled_inventory':inv(c),'compile_wall_ms':round(sum(x['elapsed_ms'] for x in chain),2),
      'compile_peak_sampled_rss_kib':max(x['peak_sampled_rss_kib'] or 0 for x in chain)}
def stdin_chain(generated_bytes):
    c=WORK/'lean-stdin';(c/'Source').mkdir(parents=True);e=leanenv(c);chain=[]
    for m,p in [('Source/Types','Types.lean'),('Source/Funs','Funs.lean'),('Source','Source.lean')]:
        row=run('stdin:lean:'+m,[LEAN,'--stdin','-o',f'{m}.olean'],c,e,generated_bytes[p])
        chain.append(row)
        if row['rc']!=0:break
    consumer=None
    if len(chain)==3 and all(x['rc']==0 for x in chain):
        write(c/'Check.lean',CHECK)
        consumer=run('stdin:lean:oracle',[LEAN,'Check.lean'],c,e)
    return {'chain_rc':[x['rc'] for x in chain],'consumer_rc':consumer['rc'] if consumer else None,
      'inventory':inv(c),'diagnostics':[{'stdout':x['stdout'],'stderr':x['stderr']} for x in chain],
      'context_equivalence_proven':False,
      'limitations':'stdin source lacks the authored filename/module-root and diagnostic path; imported context equivalence requires explicit artifact and provenance checks'}
def diagnostic_path_control(compiled):
    bad='import Source\nexample : handoff_probe.inc 0#u32 = .ok 9#u32 := by rfl\n'
    write(compiled/'CheckWrong.lean',bad)
    e=leanenv(compiled)
    file=run('diagnostic:file',[LEAN,'CheckWrong.lean'],compiled,e)
    stdin=run('diagnostic:stdin',[LEAN,'--stdin'],compiled,e,bad.encode())
    assert file['rc']!=0 and stdin['rc']!=0
    return {'file_rc':file['rc'],'stdin_rc':stdin['rc'],'file_stdout':file['stdout'],
      'stdin_stdout':stdin['stdout'],'source_sha256':sha(compiled/'CheckWrong.lean'),
      'diagnostics_byte_equal':file['stdout']==stdin['stdout']}
def pgmembers(pgid):
    p=subprocess.run(['ps','-axo','pid=,ppid=,pgid=,stat=,comm='],capture_output=True,text=True,check=True)
    rows=[]
    for line in p.stdout.splitlines():
        parts=line.strip().split(None,4)
        if len(parts)==5 and parts[2]==str(pgid):rows.append({'pid':int(parts[0]),'ppid':int(parts[1]),'stat':parts[3],'comm':parts[4]})
    return rows
def cancel_at_output(label,llbc):
    d=WORK/f'cancel-{label}';d.mkdir();fifo=d/'Funs.lean';os.mkfifo(fifo)
    argv=list(map(str,aeneas_cmd(llbc,d)));t=time.monotonic()
    p=subprocess.Popen(argv,cwd=WORK,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
    for _ in range(1500):
        if (d/'Types.lean').is_file() and p.poll() is None:break
        time.sleep(.01)
    else:raise RuntimeError('Aeneas output barrier missed')
    gate_ms=round((time.monotonic()-t)*1000,2);before=pgmembers(p.pid)
    sent=time.monotonic();os.killpg(p.pid,signal.SIGTERM);out,err=p.communicate(timeout=5)
    kill_ms=round((time.monotonic()-sent)*1000,2);time.sleep(.1);after=pgmembers(p.pid)
    assert before and not after and p.returncode!=0
    partial=inv(d);assert set(partial)=={'Types.lean'}
    fifo.unlink();retry=run(label+':aeneas-retry',aeneas_cmd(llbc,d),WORK);assert retry['rc']==0,retry
    return {'argv':argv,'pid':p.pid,'gate_ms':gate_ms,'term_to_exit_ms':kill_ms,'rc':p.returncode,
      'members_before':before,'members_after':after,'stdout':out.decode(errors='replace'),
      'stderr':err.decode(errors='replace'),'partial_inventory':partial,'retry_rc':retry['rc'],
      'retry_inventory':inv(d)}
def transfer_bench(llbc):
    target=WORK/'transfer-repeat.llbc';reads=[];copies=[];writes=[];size=llbc.stat().st_size
    for _ in range(16):
        t=time.perf_counter_ns();buf=llbc.read_bytes();reads.append(time.perf_counter_ns()-t)
        t=time.perf_counter_ns();clone=memoryview(buf).tobytes();copies.append(time.perf_counter_ns()-t)
        t=time.perf_counter_ns()
        with open(target,'wb') as f:f.write(clone);f.flush();os.fsync(f.fileno())
        writes.append(time.perf_counter_ns()-t)
    tracemalloc.start();buf=llbc.read_bytes();clone=memoryview(buf).tobytes();_,peak=tracemalloc.get_traced_memory();tracemalloc.stop()
    assert clone==llbc.read_bytes()
    return {'repetitions':16,'llbc_bytes':size,'warm_read_median_us':statistics.median(reads)/1000,
      'forced_copy_median_us':statistics.median(copies)/1000,
      'write_fsync_median_us':statistics.median(writes)/1000,'python_tracemalloc_peak_bytes':peak,
      'copied_sha256':hashlib.sha256(clone).hexdigest(),'target_sha256':sha(target)}
def source_map(llbc,generated):
    doc=json.loads(llbc.read_text());items=[]
    for item in doc['translated']['fun_decls']:
        if item:
            meta=item['item_meta'];items.append({'def_id':item['def_id'],'name':meta['name'],'span':meta.get('span')})
    funs=(generated/'Funs.lean').read_text()
    return {'charon_version':doc['charon_version'],'has_errors':doc['has_errors'],
      'source_path_in_generated':str(WORK/'source.rs') in funs,
      'generated_source_lines':[s.strip() for s in funs.splitlines() if 'Source:' in s],
      'llbc_functions':items}
def main():
    assert shutil.disk_usage(HERE).free>5*1024**3
    for p in (CHARON,AENEAS,LEAN):assert p.is_file(),p
    if WORK.exists():shutil.rmtree(WORK)
    WORK.mkdir();source=WORK/'source.rs';write(source,SOURCE)
    llbc=WORK/'source.llbc';r=run('charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,
      '--',source,'--crate-type','lib','--crate-name','handoff_probe','--edition','2021'],WORK,rustenv());assert r['rc']==0,r
    assert json.loads(llbc.read_text())['has_errors'] is False
    bench=transfer_bench(llbc)
    fileout=WORK/'generated-file';fileout.mkdir()
    file_run=run('file:aeneas',aeneas_cmd(llbc,fileout),WORK);assert file_run['rc']==0,file_run
    file_lean=compile_files('file',fileout)
    # This byte-buffer path still materializes an LLBC path: the installed CLI
    # accepts FILE, not a structured/OCaml in-memory input API.
    buffer=llbc.read_bytes();tracemalloc.start();clone=memoryview(buffer).tobytes();_,transfer_peak=tracemalloc.get_traced_memory();tracemalloc.stop()
    bufdir=WORK/'buffer-stage';bufdir.mkdir();bufllbc=bufdir/'source.llbc';t=time.perf_counter_ns();write(bufllbc,clone)
    materialize_us=(time.perf_counter_ns()-t)/1000;assert sha(bufllbc)==sha(llbc)
    bufout=WORK/'generated-buffer';bufout.mkdir()
    buffer_run=run('buffer:aeneas',aeneas_cmd(bufllbc,bufout),WORK);assert buffer_run['rc']==0,buffer_run
    generated_bytes={p.name:p.read_bytes() for p in bufout.glob('*.lean')}
    assert {p.name:p.read_bytes() for p in fileout.glob('*.lean')}==generated_bytes
    buffer_lean=compile_files('buffer',bufout)
    stdin=stdin_chain(generated_bytes)
    stdin['olean_hash_equal_to_file']={m:stdin['inventory'].get(m,{}).get('sha256')==
      file_lean['compiled_inventory'].get(m,{}).get('sha256')
      for m in ('Source/Types.olean','Source/Funs.olean','Source.olean')}
    stdin['diagnostic_path_control']=diagnostic_path_control(WORK/'lean-file')
    # The file bytes, buffer bytes, and output bytes are exact; stdout and
    # generated source comments are compared without normalizing paths.
    input_errors={}
    for label,blob in [('truncated',buffer[:len(buffer)//2]),('corrupt',b'!'+buffer[1:])]:
        d=WORK/f'{label}-llbc';d.mkdir();p=d/'source.llbc';write(p,blob)
        out=d/'generated';out.mkdir();row=run(label+':aeneas',aeneas_cmd(p,out),WORK)
        input_errors[label]={'input_sha256':sha(p),'input_bytes':len(blob),'rc':row['rc'],
           'stdout':row['stdout'],'stderr':row['stderr'],'generated':inv(out)}
        assert row['rc']!=0,input_errors[label]
    # A syntactically valid output mutation can pass Lean compilation but fail
    # the original theorem. Truncation should fail at compile time.
    text_errors={}
    for label,change in [('truncated',lambda b:b[:len(b)//2]),
                         ('semantic_mutation',lambda b:b.replace(b'1#u32',b'2#u32',1))]:
        c=WORK/f'lean-{label}';(c/'Source').mkdir(parents=True)
        for name in ('Types','Funs'):
            data=generated_bytes[f'{name}.lean']
            if name=='Funs':data=change(data)
            write(c/'Source'/f'{name}.lean',data)
        write(c/'Source.lean',generated_bytes['Source.lean']);write(c/'Check.lean',CHECK)
        e=leanenv(c);rows=[]
        for m in ('Source/Types','Source/Funs','Source'):
            row=run(label+':lean:'+m,[LEAN,'-o',f'{m}.olean',f'{m}.lean'],c,e);rows.append(row)
            if row['rc']!=0:break
        oracle=None
        if len(rows)==3 and all(x['rc']==0 for x in rows):oracle=run(label+':oracle',[LEAN,'Check.lean'],c,e)
        text_errors[label]={'compile_rcs':[x['rc'] for x in rows],
          'oracle_rc':oracle['rc'] if oracle else None,'funs_sha256':sha(c/'Source/Funs.lean'),
          'funs_bytes':(c/'Source/Funs.lean').stat().st_size,
          'diagnostics':[{'stdout':x['stdout'],'stderr':x['stderr']} for x in rows]}
    assert text_errors['truncated']['compile_rcs'][-1]!=0
    assert text_errors['semantic_mutation']['compile_rcs']==[0,0,0] and text_errors['semantic_mutation']['oracle_rc']!=0
    cancel={'file':cancel_at_output('file',llbc),'buffer':cancel_at_output('buffer',bufllbc)}
    result={'schema':1,'observed_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),
      'tools':{str(p):sha(p) for p in (CHARON,AENEAS,LEAN)},'source_sha256':sha(source),'llbc_sha256':sha(llbc),
      'llbc_bytes':llbc.stat().st_size,'transfer':bench,'buffer_stage':{'python_peak_bytes':transfer_peak,
        'materialize_us':materialize_us,'input_sha256':sha(bufllbc)},
      'file':{'aeneas':file_run,'generated':inv(fileout),'lean':file_lean},
      'buffer':{'aeneas':buffer_run,'generated':inv(bufout),'lean':buffer_lean},
      'stdin':stdin,'source_map':source_map(llbc,fileout),
      'input_errors':input_errors,'generated_text_errors':text_errors,'cancellation':cancel,
      'commands':COMMANDS,
      'boundary':'Python bytes around one-shot Aeneas CLI; no direct OCaml/library in-memory call'}
    write(HERE/'results.json',json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'ok':True,'commands':len(COMMANDS),'file_rc':file_run['rc'],'buffer_rc':buffer_run['rc'],
      'stdin':stdin['chain_rc'],'stdin_oracle':stdin['consumer_rc']}))
if __name__=='__main__':main()
