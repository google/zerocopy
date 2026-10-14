"""Run in an owned/disposable package; optional argument is existing wasm component."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,os,platform
here=Path(__file__).resolve().parent
out=here/'runs';out.mkdir(exist_ok=True)
rows=[]
def run(name,argv,env=None):
    r=subprocess.run(argv,capture_output=True,cwd=here,timeout=60,env=env)
    for key,data in [('stdout',r.stdout),('stderr',r.stderr)]:(out/(name+'.'+key)).write_bytes(data)
    rows.append({'name':name,'argv':argv,'exit':r.returncode})
    (out/'commands.json').write_text(json.dumps(rows,indent=2)+'\n')
    if r.returncode:raise SystemExit('Stopped after failure: '+name)
    return r.stdout.decode()
run('python-version',['python3','--version'])
run('rust-version',['rustc','-vV'])
run('node-version',['node','--version'])
run('node-runtime',['node','-p','JSON.stringify(process.versions)'])
run('native-cfg',['rustc','--print','cfg'])
model=json.loads(run('owned-model',['python3','primitive_model.py']))
(out/'owned-model.json').write_text(json.dumps(model,indent=2)+'\n')
run('native-build',['rustc','--edition=2024','-C','opt-level=0','-C','panic=abort','primitive.rs','-o','runs/primitive-native'])
native=json.loads(run('native-run',['./runs/primitive-native']))
expected=[1266679808,2147483648,2,255,0,0,4294967295,1,0,1,1,1,1,1,0,2143294004,1,1,1266679808,8,16,9,1,16,1,1,1,1,1,8,2147483647,1]
if native!=expected:raise SystemExit('Unexpected native result; stop and inspect')
result={'native':native,'native_expected_match':True,'owned_model':'owned-model.json','wasm_executed':False,
 'setup_diagnostic':'Initial draft used .map(primitive_case); Rust rejected extern-C fn as FnMut (E0277/E0599). Corrected to .map(|i| primitive_case(i)); no initial executable ran.'}
if len(sys.argv)>1:
    component=Path(sys.argv[1]).resolve();target=component/'lib/rustlib/wasm32-unknown-unknown'
    private=out/'sysroot';target_private=private/'lib/rustlib/wasm32-unknown-unknown'
    if not target_private.exists():shutil.copytree(target,target_private)
    run('wasm-cfg',['rustc','--print','cfg','--target','wasm32-unknown-unknown'])
    wasm_env=None
    if platform.system()=='Darwin':
        compiler_root=Path(run('rust-sysroot',['rustc','--print','sysroot']).strip())
        llvm=compiler_root/'lib/libLLVM.dylib'
        if not llvm.is_file():raise SystemExit('Matching compiler libLLVM.dylib unavailable; no wasm verdict')
        wasm_env=dict(os.environ);wasm_env['DYLD_LIBRARY_PATH']=str(compiler_root/'lib')
        linker=compiler_root/'lib/rustlib/aarch64-apple-darwin/bin/rust-lld'
        run('wasm-linker-version',[str(linker),'-flavor','wasm','--version'],env=wasm_env)
        (out/'linker-runtime.json').write_text(json.dumps({'policy':'Darwin subprocess-only DYLD_LIBRARY_PATH selects the same rustc sysroot/lib; no global changes','libLLVM_sha256':hashlib.sha256(llvm.read_bytes()).hexdigest(),'libLLVM_bytes':llvm.stat().st_size},indent=2)+'\n')
    run('wasm-build',['rustc','--edition=2024','--target','wasm32-unknown-unknown','--sysroot=runs/sysroot','--crate-type=cdylib','-C','opt-level=0','-C','panic=abort','primitive.rs','-o','runs/primitive.wasm'],env=wasm_env)
    wasm=json.loads(run('wasm-run',['node','primitive-check.mjs','runs/primitive.wasm']))
    expected_wasm=expected[:]
    for i,v in {19:4,20:8,21:5,23:8,29:4}.items():expected_wasm[i]=v
    if wasm!=expected_wasm:raise SystemExit('Unexpected wasm result; stop and inspect')
    result.update(wasm=wasm,wasm_expected_match=True,wasm_executed=True,
      wasm_sha256=hashlib.sha256((out/'primitive.wasm').read_bytes()).hexdigest(),
      component_input='Existing component supplied as argv1; copied read-only target libraries to runs/sysroot',component_source_archive_sha256='b760b0c9b08a6843c05de0098bd6802e23178ff473c4715ae57c1d679125bf22')
result['input_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in here.iterdir() if p.is_file()}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'commands':len(rows),'native_cases':len(native),'wasm_executed':result['wasm_executed'],'result':'runs/results.json'}))
