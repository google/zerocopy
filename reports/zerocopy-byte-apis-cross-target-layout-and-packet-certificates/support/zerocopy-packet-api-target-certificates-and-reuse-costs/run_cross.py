"""Run two concrete zerocopy targets with an explicit task-local wasm sysroot."""
from pathlib import Path
import hashlib,io,json,os,shutil,subprocess,sys,tarfile,tempfile,time

here=Path(__file__).resolve().parent
repo=Path(sys.argv[1]).resolve()
wasm_component=Path(sys.argv[2]).resolve()
target_lib=wasm_component/'lib/rustlib/wasm32-unknown-unknown'
if not target_lib.is_dir():raise SystemExit('Missing wasm library subject')
revision='cce761ad53785973ec2f4a6b13715b770b340c87'
archive=subprocess.run(['git','-C',str(repo),'archive',revision,'zerocopy'],capture_output=True,timeout=60)
if archive.returncode:raise SystemExit('Exact crate archive unavailable')
records=[]
with tempfile.TemporaryDirectory(prefix='zerocopy-cross-') as directory:
    root=Path(directory);source=root/'source';source.mkdir()
    with tarfile.open(fileobj=io.BytesIO(archive.stdout)) as tf:tf.extractall(source,filter='data')
    sysroot=root/'wasm-sysroot';(sysroot/'lib/rustlib').mkdir(parents=True)
    shutil.copytree(target_lib,sysroot/'lib/rustlib/wasm32-unknown-unknown')
    probe=root/'probe';(probe/'src').mkdir(parents=True)
    (probe/'Cargo.toml').write_text('''[package]
name = "packet-api-controls"
version = "0.0.0"
edition = "2024"
[workspace]
[lib]
crate-type = ["cdylib", "rlib"]
[dependencies]
zerocopy = { path = "../source/zerocopy" }
''')
    for name in ['lib.rs','main.rs']:shutil.copy2(here/name,probe/'src'/name)
    env=os.environ.copy();env['CARGO_TARGET_DIR']=str(root/'target');env['CARGO_TERM_COLOR']='never'
    env['CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUSTFLAGS']='--sysroot='+str(sysroot)
    wasm=root/'target/wasm32-unknown-unknown/debug/packet_api_controls.wasm'
    commands=[('rust-version',['rustc','-vV']),('node-version',['node','--version']),
        ('native-build',['cargo','build','--bin','packet-api-controls','--offline','--quiet']),
        ('native-check',[str(root/'target/debug/packet-api-controls')]),
        ('wasm-build',['cargo','build','--lib','--target','wasm32-unknown-unknown','--offline','--quiet']),
        ('wasm-check',['node',str(here/'check-wasm.mjs'),str(wasm)])]
    for name,args in commands:
        start=time.monotonic_ns();r=subprocess.run(args,cwd=probe,env=env,capture_output=True,timeout=120);elapsed=time.monotonic_ns()-start
        for stream,data in [('stdout',r.stdout),('stderr',r.stderr)]:
            (here/(name+'.'+stream)).write_bytes(data.replace(str(root).encode(),b'<private-extraction>'))
        row={'name':name,'exit':r.returncode,'elapsed_ns':elapsed,'argv':[s.replace(str(root),'<private-extraction>').replace(str(here),'<support>') for s in args]};records.append(row)
        print(json.dumps(row),flush=True)
        if r.returncode:break
    if wasm.exists():
        wasm_digest=hashlib.sha256(wasm.read_bytes()).hexdigest();wasm_size=wasm.stat().st_size
    else:wasm_digest=None;wasm_size=None
    if (probe/'Cargo.lock').exists():shutil.copy2(probe/'Cargo.lock',here/'Cargo.lock')
result={'revision':revision,'source_archive_sha256':hashlib.sha256(archive.stdout).hexdigest(),
    'owned_input_sha256':{n:hashlib.sha256((here/n).read_bytes()).hexdigest() for n in ['lib.rs','main.rs','check-wasm.mjs','run_cross.py']},
    'commands':records,'wasm_sha256':wasm_digest,'wasm_bytes':wasm_size,
    'scope':'Concrete composed packet API controls; separate logical model certificates are measured by another driver',
    'network':'Cargo offline; official target component acquired separately'}
(here/'results.json').write_text(json.dumps(result,indent=2)+'\n')
if len(records)!=6 or any(r['exit'] for r in records):raise SystemExit('Incomplete execution; preserve diagnostics')
