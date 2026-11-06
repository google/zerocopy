#!/usr/bin/env python3
"""Tiny annotation locator model plus real Rust/Cargo/Charon and Lean controls."""
import hashlib, json, os, platform, re, shutil, subprocess, sys, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
WORK=HERE/'work'; VERS=HERE/'versions'; ART=HERE/'artifacts'
TOOLS=Path('/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools')
RUSTBIN=TOOLS/'rustup/toolchains/nightly-2026-05-31-aarch64-apple-darwin/bin'
CARGO=RUSTBIN/'cargo'; RUSTC=RUSTBIN/'rustc'; CHARON=TOOLS/'bin/charon'
LEAN=TOOLS/'elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin/lean'
BASE='''#![allow(dead_code)]
pub const SOURCE: &str = include_str!("lib.rs");
pub const BUILD_PROOF: &str = env!("PROOF_STAMP");
pub fn source_len() -> usize { SOURCE.len() }

//% begin shared scope=module
//% def helper : Nat := 7
//% end

pub mod left {
    //% begin claim-a scope=next
    //% namespace Left
    //% theorem checked : helper = 7 := by rfl
    //% end Left
    //% end
    /// proof-id: claim-a
    pub fn alpha() -> u32 { 7 }
}

pub mod right {
    //% begin claim-b scope=next
    //% namespace Right
    //% theorem checked : helper = 7 := by rfl
    //% end Right
    //% end
    /// proof-id: claim-b
    pub fn beta() -> u32 { 7 }
}

//% begin selected scope=next
//% namespace Selected
//% theorem checked : helper = 7 := by rfl
//% end Selected
//% end
#[cfg(feature = "selected")]
/// proof-id: selected
pub fn selected_only() -> u32 { 7 }

#[cfg(test)]
mod tests {
    //% begin test-only scope=next
    //% namespace Test
    //% theorem checked : helper = 7 := by rfl
    //% end Test
    //% end
    /// proof-id: test-only
    pub fn test_only() -> u32 { 7 }
    #[test] fn smoke() { assert_eq!(test_only(), 7); }
}
'''
BUILD_RS='''use std::{env,fs,path::Path};
fn main() {
  let p = Path::new("src/lib.rs");
  println!("cargo:rerun-if-changed={}", p.display());
  let s = fs::read_to_string(p).unwrap();
  let sum: u64 = s.lines().filter(|l| l.trim_start().starts_with("//% "))
    .flat_map(|l| l.bytes()).map(u64::from).sum();
  println!("cargo:rustc-env=PROOF_STAMP={sum}");
  println!("cargo:warning=proof-stamp:{sum}");
  let _ = env::var("OUT_DIR").unwrap();
}
'''
EVENTS=[];START=time.monotonic()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def log(kind,**kw):EVENTS.append(dict(seq=len(EVENTS),ms=round((time.monotonic()-START)*1000,1),kind=kind,**kw))
def command(label,args,cwd,env=None,timeout=55):
    st=time.monotonic()
    try:
        p=subprocess.run(list(map(str,args)),cwd=cwd,env=env,capture_output=True,text=True,timeout=timeout)
        rc,out,err=p.returncode,p.stdout,p.stderr
    except subprocess.TimeoutExpired as e:
        rc='timeout';out=(e.stdout or b'').decode(errors='replace');err=(e.stderr or b'').decode(errors='replace')
    row=dict(label=label,argv=list(map(str,args)),cwd=str(cwd),rc=rc,elapsed_ms=round((time.monotonic()-st)*1000,1),stdout=out,stderr=err)
    log('command',**row);return row
def variants():
    before,left_and_rest=BASE.split('pub mod left {',1)
    left_body,after=left_and_rest.split('\n\npub mod right {',1)
    moved=before+'pub mod right {'+after+'\n\npub mod relocated {'+left_body.replace('namespace Left','namespace Relocated').replace('end Left','end Relocated')+'\n'
    dup=BASE.replace('pub mod right {','''pub mod copied {
    //% begin claim-a scope=next
    //% namespace Copied
    //% theorem checked : helper = 7 := by rfl
    //% end Copied
    //% end
    /// proof-id: claim-a
    pub fn alpha_copy() -> u32 { 7 }
}

pub mod right {''')
    malformed=BASE.replace('pub fn alpha() -> u32 { 7 }','pub fn alpha( -> u32 { 7 }')
    unfinished=BASE+'\n//% begin orphan scope=next\n//% theorem unfinished : True := by\n'
    proofedit=BASE.replace('theorem checked : helper = 7 := by rfl','theorem checked : helper = 7 := by exact rfl',1)
    return {'baseline':BASE,'moved':moved,'duplicated':dup,'malformed':malformed,'unfinished':unfinished,'proof-edit':proofedit}
def locate(text):
    """Explicit minimal line-marker model; never treated as Anneal parsing."""
    lines=text.splitlines(keepends=True);blocks=[];start=None;payload=[];line_start=0
    for i,line in enumerate(lines,1):
        clean=line.lstrip();m=re.match(r'//% begin ([\w-]+) scope=(\w+)',clean)
        if m:
            if start is not None:blocks.append(dict(id=start[0],scope=start[1],start_line=start[2],end_line=i-1,status='incomplete',payload=payload))
            start=(m.group(1),m.group(2),i);payload=[];continue
        if start is None:continue
        if clean.startswith('//% end') and clean.strip()=='//% end':
            blocks.append(dict(id=start[0],scope=start[1],start_line=start[2],end_line=i,status='complete',payload=payload))
            start=None;payload=[];continue
        if clean.startswith('//% '):payload.append(clean[4:].rstrip('\n'))
        else:
            blocks.append(dict(id=start[0],scope=start[1],start_line=start[2],end_line=i,status='malformed',payload=payload));start=None;payload=[]
    if start is not None:blocks.append(dict(id=start[0],scope=start[1],start_line=start[2],end_line=len(lines),status='incomplete',payload=payload))
    for b in blocks:
        b['tentative_next_fn']=None
        if b['scope']=='next' and b['status']=='complete':
            for line in lines[b['end_line']:b['end_line']+7]:
                m=re.search(r'\b(?:pub\s+)?fn\s+(\w+)\s*\(',line)
                if m:b['tentative_next_fn']=m.group(1);break
    return blocks
def project(blocks):
    return '\n'.join('\n'.join(b['payload']) for b in blocks if b['status']=='complete')+'\n'
def names(parts):return '::'.join(x['Ident'][0] if 'Ident' in x else '<'+next(iter(x))+'>' for x in parts)
def llbc(path):
    data=json.loads(path.read_text());crate=data['translated'];fs=[];fun=[]
    for f in crate['files']:fs.append(dict(id=f['id'],name=f['name'],sha256=hashlib.sha256(f['contents'].encode()).hexdigest() if f.get('contents') is not None else None))
    for d in crate['fun_decls']:
        if not d:continue
        m=d.get('item_meta') or {}
        if not m.get('is_local'):continue
        attrs=m.get('attr_info',{}).get('attributes',[])
        markers=[a['DocComment'].strip() for a in attrs if isinstance(a,dict) and 'DocComment' in a and 'proof-id:' in a['DocComment']]
        fun.append(dict(id=d['def_id'],name=names(m['name']),markers=markers,span=m.get('span')))
    return dict(sha256=sha(path),has_errors=data['has_errors'],crate_name=crate['crate_name'],files=fs,functions=fun)
def main():
    for p in [WORK,VERS,ART]:
        if p.exists():shutil.rmtree(p)
        p.mkdir(parents=True)
    fixture=WORK/'fixture';(fixture/'src').mkdir(parents=True);(fixture/'examples').mkdir(parents=True)
    (fixture/'Cargo.toml').write_text('[package]\nname = "annotation_boundary_probe"\nversion = "0.1.0"\nedition = "2021"\nbuild = "build.rs"\n\n[features]\ndefault = []\nselected = []\n')
    (fixture/'Cargo.lock').write_text('# This file is automatically @generated by Cargo.\n# It is not intended for manual editing.\nversion = 4\n\n[[package]]\nname = "annotation_boundary_probe"\nversion = "0.1.0"\n')
    (fixture/'build.rs').write_text(BUILD_RS)
    (fixture/'examples/observe.rs').write_text('fn main(){println!("len={} stamp={}", annotation_boundary_probe::source_len(), annotation_boundary_probe::BUILD_PROOF);}\n')
    vv=variants()
    for name,text in vv.items():(VERS/(name+'.rs')).write_text(text)
    src=fixture/'src/lib.rs'
    env=dict(os.environ,RUSTUP_HOME=str(TOOLS/'rustup'),CARGO_HOME=str(TOOLS/'cargo'),CHARON_TOOLCHAIN_IS_IN_PATH='1')
    env['PATH']=os.pathsep.join([str(RUSTBIN),str(TOOLS/'bin'),env.get('PATH','')]);env['CARGO_NET_OFFLINE']='true'
    log('subject',platform=platform.platform(),python=sys.version,tools={n:dict(path=str(p),sha256=sha(p),version=command('version-'+n,[p,'--version'],fixture,env,8)['stdout'].strip()) for n,p in [('rustc',RUSTC),('cargo',CARGO),('charon',CHARON),('lean',LEAN)]},fixture_hashes={k:sha(VERS/(k+'.rs')) for k in vv})
    for name,text in vv.items():
        blocks=locate(text);lean=project(blocks);(ART/(name+'.lean')).write_text(lean)
        log('locator',variant=name,source_sha256=sha(VERS/(name+'.rs')),blocks=blocks,projection_sha256=sha(ART/(name+'.lean')))
        if name in ('baseline','proof-edit','moved','duplicated'):
            command('lean-'+name,[LEAN,ART/(name+'.lean')],fixture,env,20)
        src.write_text(text)
        rustenv=dict(env,PROOF_STAMP='direct-rustc')
        command('rustc-'+name,[RUSTC,'--crate-type','lib','--edition=2021','--emit=metadata','-o',ART/(name+'.rmeta'),src],fixture,rustenv,20)
    # Cargo's build script and include_str! see a comment-only annotation edit.
    for name in ['baseline','proof-edit']:
        src.write_text(vv[name]);runenv=dict(env,CARGO_TARGET_DIR=str(WORK/'cargo-target'))
        command('cargo-observe-'+name,[CARGO,'run','--offline','--locked','--quiet','--example','observe'],fixture,runenv,40)
    # Charon captures compiler-derived candidates for exactly selected Cargo subjects.
    subjects=[('baseline-lib','baseline',['--lib']),('baseline-selected','baseline',['--lib','--features','selected']),('baseline-tests','baseline',['--tests']),('moved-lib','moved',['--lib']),('duplicated-lib','duplicated',['--lib']),('malformed-lib','malformed',['--lib'])]
    for label,version,flags in subjects:
        src.write_text(vv[version]);target=WORK/('charon-target-'+label);output=ART/(label+'.llbc')
        runenv=dict(env,CARGO_TARGET_DIR=str(target))
        result=command('charon-'+label,[CHARON,'cargo','--preset','aeneas','--dest-file',output,'--','--manifest-path',fixture/'Cargo.toml',*flags,'--offline','--locked'],fixture,runenv,45)
        log('charon_result',label=label,variant=version,source_sha256=sha(src),rc=result['rc'],projection=llbc(output) if output.exists() else None)
        if target.exists():shutil.rmtree(target)
    src.write_text(vv['baseline'])
    if (WORK/'cargo-target').exists():shutil.rmtree(WORK/'cargo-target')
    (HERE/'raw-results.json').write_text(json.dumps(EVENTS,indent=2)+'\n')
    print(json.dumps({'events':len(EVENTS),'raw_sha256':sha(HERE/'raw-results.json'),'script_sha256':sha(Path(__file__))},indent=2))
if __name__=='__main__':main()
