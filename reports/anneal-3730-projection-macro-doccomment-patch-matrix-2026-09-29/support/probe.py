#!/usr/bin/env python3
"""Real compiler specimens plus an explicitly illustrative projection/patch model."""
import hashlib, json, os, pathlib, platform, random, statistics, subprocess, time

HERE = pathlib.Path(__file__).resolve().parent
TOOLS = pathlib.Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RBIN = TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
RLIB = TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/lib'
CHARON = TOOLS/'bin/charon'
LEAN = TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'
RUSTFMT = pathlib.Path('/opt/homebrew/bin/rustfmt')

def digest(x):
    if isinstance(x, pathlib.Path): x=x.read_bytes()
    if isinstance(x, str): x=x.encode()
    return hashlib.sha256(x).hexdigest()

def run(label, argv, env=None):
    p=subprocess.run([str(x) for x in argv], cwd=HERE, env=env, capture_output=True,text=True,timeout=60)
    return {'label':label,'argv':[str(x).replace(str(HERE),'$REPORT') for x in argv],
            'exit':p.returncode,'stdout':p.stdout.replace(str(HERE),'$REPORT'),
            'stderr':p.stderr.replace(str(HERE),'$REPORT')}

def project(src):
    """Invented `///| ` projection: three doc blocks, A repeated, B+C joined."""
    b=src.encode(); lines=b.splitlines(keepends=True); groups=[]; active=[]; at=0
    for line in lines:
        if line.startswith(b'///| '):
            active.append((at+5,at+len(line),line[5:]))
        elif active:
            groups.append(active);active=[]
        at+=len(line)
    if active:groups.append(active)
    assert len(groups)==3 and [len(g) for g in groups]==[2,2,2]
    out=bytearray();maps=[]
    def synthetic(t):out.extend(t.encode())
    def copy(group, obligation):
        for s,e,payload in groups[group]:
            g=len(out);out.extend(payload)
            maps.append({'source':[s,e],'generated':[g,len(out)],'owner':f'doc-{group}',
                         'obligation':obligation,'exact':True})
    synthetic('import Lean\n\n')
    synthetic('theorem left : True := ');copy(0,'left');synthetic('\n')
    synthetic('theorem right : True := ');copy(0,'right');synthetic('\n')
    synthetic('theorem combined : True ∧ True := ');copy(1,'combined');copy(2,'combined')
    return {'text':out.decode(),'maps':maps,'source_sha256':digest(b),'text_sha256':digest(bytes(out))}

def find_generated(p,needle,obligation=None):
    b=p['text'].encode();n=needle.encode(); hits=[];start=0
    while (start:=b.find(n,start))>=0:
        end=start+len(n)
        for m in p['maps']:
            if m['generated'][0]<=start and end<=m['generated'][1] and (obligation is None or obligation==m['obligation']):
                hits.append((start,end,m));break
        start=end
    return hits

def apply_patch(src,p,revision,action):
    if action['revision']!=revision or action['source_sha256']!=digest(src) or action['text_sha256']!=p['text_sha256']:
        return None,'stale-generation'
    if action.get('resource_operations'):return None,'resource-operation-unsupported'
    chosen=[]
    for ed in action['edits']:
        if ed.get('revision',revision)!=revision:return None,'mixed-generation'
        if ed.get('uri')!='projection://proof':return None,'read-only-or-external-uri'
        if ed.get('snippet') or '$' in ed['new']:return None,'snippet-unsupported'
        gs,ge=ed['range'];matches=[m for m in p['maps'] if m['generated'][0]<=gs and ge<=m['generated'][1]
                                      and (gs!=ge or m['generated'][0]<gs<m['generated'][1])]
        if len(matches)!=1:return None,'no-exact-single-origin'
        m=matches[0];ss=m['source'][0]+gs-m['generated'][0];se=ss+ge-gs
        if src.encode()[ss:se]!=p['text'].encode()[gs:ge]:return None,'expected-source-bytes-mismatch'
        chosen.append((ss,se,ed['new'].encode()))
    dedup={}
    for s,e,new in chosen:
        if (s,e) in dedup and dedup[s,e]!=new:return None,'conflicting-duplicate-origin'
        dedup[s,e]=new
    ordered=sorted((s,e,new) for (s,e),new in dedup.items())
    if any(ordered[i][1]>ordered[i+1][0] for i in range(len(ordered)-1)):
        return None,'overlapping-source-edits'
    b=src.encode()
    for s,e,new in reversed(ordered):b=b[:s]+new+b[e:]
    return b.decode(),'applied'

def action(src,p,revision,edits,**kw):
    return {'revision':revision,'source_sha256':digest(src),'text_sha256':p['text_sha256'],
            'edits':edits,**kw}

def edit(span,new,uri='projection://proof',**kw):return {'uri':uri,'range':list(span),'new':new,**kw}

def classify_diagnostics(messages,projection,category):
    rows=[];lines=projection['text'].encode().splitlines(keepends=True)
    for msg in messages:
        pos=msg.get('pos') or {};line=pos.get('line');col=pos.get('column')
        offset=None if not isinstance(line,int) or line<1 or line>len(lines) else sum(len(x) for x in lines[:line-1])+col
        owners=[] if offset is None else [m for m in projection['maps'] if m['generated'][0]<=offset<m['generated'][1]]
        row={'lean_file':msg.get('fileName'),'lean_position':pos,'severity':msg.get('severity'),
             'message':msg.get('data'),'category':category}
        if len(owners)==1:
            m=owners[0];row.update({'responsibility':'exact-authored-candidate',
                 'source_byte':m['source'][0]+offset-m['generated'][0],
                 'owner':m['owner'],'obligation':m['obligation']})
        else:row['responsibility']='generated-or-unmapped'
        rows.append(row)
    return rows

def indexed_update(src,p,ss,se,repl):
    """Narrow fast path for one within-line source edit; updates all repeated generated copies."""
    old=src.encode();replacement=repl.encode();delta=len(replacement)-(se-ss)
    containing=[m for m in p['maps'] if m['source'][0]<=ss and se<=m['source'][1]]
    assert containing and b'\n' not in old[ss:se] and b'\n' not in replacement
    gedits=sorted((m['generated'][0]+ss-m['source'][0],m['generated'][0]+se-m['source'][0]) for m in containing)
    text=p['text'].encode()
    for gs,ge in reversed(gedits):text=text[:gs]+replacement+text[ge:]
    nsrc=old[:ss]+replacement+old[se:]
    maps=[]
    for m in p['maps']:
        x=dict(m);s,e=m['source'];g,h=m['generated']
        if e<=ss:pass
        elif s>=se:s+=delta;e+=delta
        else:assert s<=ss and se<=e;e+=delta
        g+=sum(delta for a,z in gedits if z<=g)
        h+=sum(delta for a,z in gedits if z<=h)
        x['source']=[s,e];x['generated']=[g,h];maps.append(x)
    return nsrc.decode(),{'text':text.decode(),'maps':maps,'source_sha256':digest(nsrc),'text_sha256':digest(text)}

def main():
    records=[];src=(HERE/'fixture.rs').read_text();p=project(src)
    env=dict(os.environ);env.update({'RUSTUP_HOME':str(TOOLS/'rustup'),'CARGO_HOME':str(TOOLS/'cargo'),
        'CHARON_TOOLCHAIN_IS_IN_PATH':'1','PATH':os.pathsep.join([str(RBIN),str(TOOLS/'bin'),env.get('PATH','')]),
        'DYLD_LIBRARY_PATH':os.pathsep.join([str(RLIB),str(RLIB/'rustlib/aarch64-apple-darwin/lib'),env.get('DYLD_LIBRARY_PATH','')])})
    llbc=HERE/'fixture.llbc';llbc.unlink(missing_ok=True)
    records.append(run('rustc', [RBIN/'rustc','--crate-type','lib','--edition','2021','--crate-name','projection_fixture',HERE/'fixture.rs','--emit','metadata','-o',HERE/'fixture.rmeta'],env))
    assert records[-1]['exit']==0,records[-1]
    records.append(run('charon',[CHARON,'rustc','--preset','aeneas','--dest-file',llbc,'--',HERE/'fixture.rs','--crate-type','lib','--crate-name','projection_fixture','--edition','2021'],env))
    assert records[-1]['exit']==0 and llbc.exists(),records[-1]
    meta=json.loads(llbc.read_text());assert meta['has_errors'] is False
    funs=[]
    for x in meta['translated']['fun_decls']:
        if x:
            names=[v['Ident'][0] for v in x['item_meta']['name'] if 'Ident' in v]
            if names and names[-1] in ('annotated','first','second','macro_generated'):
                funs.append({'name':names[-1],'span':x['item_meta']['span'],
                    'source_text':x['item_meta'].get('source_text'),'generated_from_span':x['item_meta'].get('generated_from_span')})
    assert {x['name'] for x in funs}=={'annotated','first','second','macro_generated'}
    formatted=HERE/'formatted-fixture.rs';formatted.write_text(src)
    records.append(run('rustfmt',[RUSTFMT,formatted]));assert records[-1]['exit']==0
    fp=project(formatted.read_text());assert fp['text']==p['text'] and fp['source_sha256']!=p['source_sha256']
    # The projected text is real Lean source, but the projector is illustrative.
    generated=HERE/'generated.lean';generated.write_text(p['text'])
    records.append(run('lean-baseline',[LEAN,'--json',generated]));assert records[-1]['exit']==0,records[-1]
    a=find_generated(p,'trivial','left')[0];b=find_generated(p,'trivial','combined')[0]
    multi=action(src,p,1,[edit(a[:2],'simp'),edit(b[:2],'simp')])
    patched,status=apply_patch(src,p,1,multi);assert status=='applied' and patched!=src
    pp=project(patched);assert pp['text'].count('simp')==3 and 'theorem combined' in pp['text']
    patched_file=HERE/'patched.lean';patched_file.write_text(pp['text'])
    records.append(run('lean-patched-multi-range',[LEAN,'--json',patched_file]));assert records[-1]['exit']==0,records[-1]
    controls={}
    def check(name,base,proj,rev,act,expected):
        next_src,reason=apply_patch(base,proj,rev,act)
        assert reason==expected and next_src is None,(name,reason)
        controls[name]=reason
    shifted='// shifted host-only comment\n'+src
    check('host-shift-same-projection',shifted,project(shifted),2,multi,'stale-generation')
    check('A-B-A-revision',src,p,3,multi,'stale-generation')
    check('mixed-edit-revisions',src,p,1,action(src,p,1,[edit(a[:2],'simp'),edit(b[:2],'simp',revision=2)]),'mixed-generation')
    duplicate=find_generated(p,'trivial','right')[0]
    check('conflicting-duplicate',src,p,1,action(src,p,1,[edit(a[:2],'simp'),edit(duplicate[:2],'aesop')]),'conflicting-duplicate-origin')
    header=(p['text'].encode().find(b'import Lean'),p['text'].encode().find(b'import Lean')+6)
    check('synthetic-header',src,p,1,action(src,p,1,[edit(a[:2],'simp'),edit(header,'open')]),'no-exact-single-origin')
    gap=(a[1],duplicate[0])
    check('cross-generated-gap',src,p,1,action(src,p,1,[edit(gap,'')]),'no-exact-single-origin')
    check('generated-model-URI',src,p,1,action(src,p,1,[edit(a[:2],'simp'),edit(b[:2],'x',uri='file:///GeneratedModel.lean')]),'read-only-or-external-uri')
    check('snippet-placeholder',src,p,1,action(src,p,1,[edit(a[:2],'${1:simp}',snippet=True)]),'snippet-unsupported')
    check('resource-rename',src,p,1,action(src,p,1,[edit(a[:2],'simp')],resource_operations=['rename file:///GeneratedModel.lean']),'resource-operation-unsupported')
    deleted=src.replace('///|   trivial\n','',1)
    # A deleted owner makes the projection structurally invalid in this strict fixture.
    owner_delete={'old_source_sha256':digest(src),'new_source_sha256':digest(deleted),
                  'strict_project_rejected':False}
    try:project(deleted)
    except AssertionError:owner_delete['strict_project_rejected']=True
    assert owner_delete['strict_project_rejected']
    # Real Lean diagnostics in copied authored text and synthetic scaffold.
    bad=src.replace('///|   trivial','///|   missingProof',1)
    bad_project=project(bad);bad_file=HERE/'bad-authored.lean';bad_file.write_text(bad_project['text'])
    records.append(run('lean-authored-diagnostic',[LEAN,'--json',bad_file]));assert records[-1]['exit']!=0
    synthetic=p['text'].replace('theorem left : True :=','theorem left : MissingGeneratedType :=',1)
    synthetic_file=HERE/'bad-synthetic.lean';synthetic_file.write_text(synthetic)
    records.append(run('lean-synthetic-diagnostic',[LEAN,'--json',synthetic_file]));assert records[-1]['exit']!=0
    authored_json=[json.loads(x) for x in records[-2]['stdout'].splitlines() if x.startswith('{')]
    synthetic_json=[json.loads(x) for x in records[-1]['stdout'].splitlines() if x.startswith('{')]
    assert any('unknown tactic' in x.get('data','') for x in authored_json)
    assert any('MissingGeneratedType' in x.get('data','') for x in synthetic_json)
    authored_class=classify_diagnostics(authored_json,bad_project,'projected-proof')
    synthetic_class=classify_diagnostics(synthetic_json,p,'synthetic-wrapper-type-error')
    assert any(x['responsibility']=='exact-authored-candidate' for x in authored_class)
    assert any(x['responsibility']=='generated-or-unmapped' for x in synthetic_class)
    model_file=HERE/'bad-generated-model.lean';model_file.write_text('def modelValue : Nat := missingModelValue\n')
    external_file=HERE/'bad-external-import.lean';external_file.write_text('import MissingExternalDependency\n')
    records.append(run('lean-generated-model-diagnostic',[LEAN,'--json',model_file]));assert records[-1]['exit']!=0
    records.append(run('lean-external-import-diagnostic',[LEAN,'--json',external_file]));assert records[-1]['exit']!=0
    model_json=[json.loads(x) for x in records[-2]['stdout'].splitlines() if x.startswith('{')]
    external_json=[json.loads(x) for x in records[-1]['stdout'].splitlines() if x.startswith('{')]
    assert model_json and external_json
    # A measured edit stream uses duplicate-aware indexed updates, then a full rebuild oracle.
    state_src=src;state=p;rng=random.Random(3730);fast_ns=[];full_ns=[];steps=[]
    for i in range(80):
        owner='doc-0' if rng.random()<.5 else 'doc-2'
        candidates=[m for m in state['maps'] if m['owner']==owner]
        m=next(x for x in candidates if any(token in state_src.encode()[slice(*x['source'])] for token in (b'trivial',b'simp')))
        segment=state_src.encode()[slice(*m['source'])]
        old=b'trivial' if b'trivial' in segment else b'simp'
        new='simp' if old==b'trivial' else 'trivial'
        s=m['source'][0]+segment.index(old);e=s+len(old)
        t=time.perf_counter_ns();state_src,state=indexed_update(state_src,state,s,e,new);fast_ns.append(time.perf_counter_ns()-t)
        t=time.perf_counter_ns();oracle=project(state_src);full_ns.append(time.perf_counter_ns()-t)
        assert state==oracle,(i,state,oracle)
        steps.append({'step':i,'owner':owner,'old':old.decode(),'new':new,'text_sha256':state['text_sha256'],
                      'source_sha256':state['source_sha256']})
    result={'environment':{'platform':platform.platform(),'python':platform.python_version(),
              'rustc_sha256':digest(RBIN/'rustc'),'charon_sha256':digest(CHARON),'lean_sha256':digest(LEAN),
              'rustfmt_sha256':digest(RUSTFMT)},'specimen':{'source_sha256':digest(src),
              'llbc_sha256':digest(llbc),'formatted_source_sha256':digest(formatted),
              'generated_sha256':p['text_sha256'],'maps':p['maps'],'charon_functions':funs,
              'authored_one_to_many':{'doc-0':['left','right']},
              'combined_many_to_one':{'combined':['doc-1','doc-2']}},
            'patch':{'multi_range_status':status,'patched_source_sha256':digest(patched),
                     'patched_generated_sha256':pp['text_sha256'],'controls':controls,
                     'owner_delete':owner_delete},
            'diagnostics':{'authored':authored_json,'synthetic':synthetic_json,
                           'generated_model':model_json,'external_import':external_json,
                           'authored_location_classification':authored_class,
                           'synthetic_location_classification':synthetic_class,
                           'generated_model_responsibility':'generated model URI; no writable Rust range',
                           'external_import_responsibility':'dependency/import URI; no writable Rust range'},
            'edit_stream':{'seed':3730,'steps':steps,'fast_median_us':statistics.median(fast_ns)/1000,
                           'full_median_us':statistics.median(full_ns)/1000,
                           'fast_total_ms':sum(fast_ns)/1e6,'full_total_ms':sum(full_ns)/1e6,
                           'all_equal':True},'records':records}
    (HERE/'raw-results.json').write_text(json.dumps(result,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
    print(json.dumps({'functions':len(funs),'maps':len(p['maps']),'controls':len(controls),
                      'edit_steps':len(steps),'fast_median_us':result['edit_stream']['fast_median_us'],
                      'full_median_us':result['edit_stream']['full_median_us']},sort_keys=True))

if __name__=='__main__':main()
