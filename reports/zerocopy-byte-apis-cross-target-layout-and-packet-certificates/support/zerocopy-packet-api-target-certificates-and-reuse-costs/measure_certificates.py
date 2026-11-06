"""Measure an owned model/ABI certificate, not Rust frontend correctness."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time,statistics,sys
p=Path(__file__).resolve().parent
lean=Path(sys.argv[1]).resolve();out=Path(sys.argv[2]).resolve();out.mkdir(exist_ok=False)
source_sha=hashlib.sha256((p/'lib.rs').read_bytes()).hexdigest()
model_sha=hashlib.sha256((p/'PacketModel.lean').read_bytes()).hexdigest()
(out/'PacketModel.lean').write_bytes((p/'PacketModel.lean').read_bytes())
env=dict(os.environ,LEAN_PATH=str(out));rows=[]
def run(name,argv):
 start=time.monotonic_ns();r=subprocess.run(argv,cwd=out,env=env,capture_output=True,timeout=30)
 elapsed=time.monotonic_ns()-start
 (out/(name+'.stdout')).write_bytes(r.stdout);(out/(name+'.stderr')).write_bytes(r.stderr)
 row={'phase':name,'exit':r.returncode,'elapsed_ns':elapsed};rows.append(row);return r
r=run('shared-model',[str(lean),'-o','PacketModel.olean','PacketModel.lean'])
if r.returncode:raise SystemExit('model rejected')
assert b'sorryAx' not in r.stdout
raw=(p/'native-check.stdout').read_text();native_layout=json.loads(re.search(r'layout=(\[[^\n]*\])',raw).group(1))
wasm=json.loads((p/'wasm-check.stdout').read_text());layouts={'aarch64-apple-darwin':native_layout,'wasm32-unknown-unknown':wasm['layout']}
def certificate(layout,expected_word):
 return '''import PacketModel\nnamespace Receipt\ndef observedLayout : List Nat := %s\ndef expectedSource : String := "%s"\ndef capturedSource : String := "%s"\ntheorem layout_agrees : observedLayout = Packet.expectedLayout %s := rfl\ntheorem source_index : capturedSource = expectedSource := rfl\ntheorem bounded_machine_length (n : Nat) (h : n ≤ 64) : 6+n < %s := by omega\ntheorem all_payloads (flags payload destination : List Packet.Byte) (valid : Packet.validFlags flags = true) (capacity : payload.length ≤ destination.length) : Packet.process flags payload destination true = some (payload ++ destination.drop payload.length) := Packet.pipeline_success flags payload destination valid capacity\n#print axioms layout_agrees\n#print axioms source_index\n#print axioms bounded_machine_length\n#print axioms all_payloads\nend Receipt\n'''%(str(layout),source_sha,source_sha,expected_word,2**(expected_word*8))
sizes={}
for target,layout in layouts.items():
 for i in range(3):
  name=target.replace('-','_')+'_'+str(i);start=time.monotonic_ns();text=certificate(layout,layout[0]);f=out/(name+'.lean');f.write_text(text);gen=time.monotonic_ns()-start
  rows.append({'phase':'generate','target':target,'sample':i,'elapsed_ns':gen,'certificate_bytes':len(text.encode())})
  r=run(name,[str(lean),'-o',name+'.olean',name+'.lean'])
  if r.returncode or b'sorryAx' in r.stdout:raise SystemExit('certificate rejected: '+name)
  sizes[target]=(out/(name+'.olean')).stat().st_size
for name,layout,word in [('wrong_target',native_layout,4),('wrong_type',[native_layout[0],8,1,2,1],native_layout[0])]:
 (out/(name+'.lean')).write_text(certificate(layout,word));r=run(name,[str(lean),name+'.lean'])
 if r.returncode==0:raise SystemExit('negative unexpectedly accepted')
consumer={'source_sha256':source_sha,'model_sha256':model_sha,'max_payload':64,'targets':layouts}
(out/'consumer.json').write_text(json.dumps(consumer,indent=2)+'\n')
changed_source=hashlib.sha256((p/'lib.rs').read_bytes()+b'\n// changed subject\n').hexdigest()
controls={'source_change_rejected':changed_source!=source_sha,'narrow_domain_rejected':32!=consumer['max_payload'],'different_model_rejected':hashlib.sha256((p/'PacketModel.lean').read_bytes()+b'\n').hexdigest()!=model_sha}
if not all(controls.values()):raise SystemExit('binding control failed')
result={'source_sha256':source_sha,'model_sha256':model_sha,'runs':rows,'compiled_receipt_sizes':sizes,'binding_controls':controls,'model_olean_bytes':(out/'PacketModel.olean').stat().st_size,'scope':'Template generation and model/ABI theorem checking; manual Rust import, raw observations and compiler/runtime remain trusted. Native loops are not logical proofs. Three samples, uncontrolled shared caches/load.'}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'source_sha256':source_sha,'runs':len(rows),'targets':layouts,'binding_controls':controls,'all_expected':True}))
