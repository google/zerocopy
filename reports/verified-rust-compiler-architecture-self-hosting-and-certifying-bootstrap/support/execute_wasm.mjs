import fs from 'node:fs';
import crypto from 'node:crypto';
import { performance } from 'node:perf_hooks';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
const dir=path.dirname(fileURLToPath(import.meta.url));
const bytes=fs.readFileSync(path.join(dir,'boolean4.wasm'));
const literal=JSON.parse(fs.readFileSync(path.join(dir,'module-bytes.json'),'utf8'));
if(!bytes.equals(Buffer.from(literal)))throw new Error('literal/file mismatch');
const t=performance.now();const module=new WebAssembly.Module(bytes);const compileMs=performance.now()-t;
const ti=performance.now();const instance=new WebAssembly.Instance(module,{});const instantiateMs=performance.now()-ti;
const imports=WebAssembly.Module.imports(module),exports=WebAssembly.Module.exports(module);
if(imports.length!==0)throw new Error('unexpected imports');
const validate=instance.exports.validate;
const samples=[];
for(let a=0;a<4;a++)for(let b=0;b<4;b++)for(let c=0;c<4;c++)for(let d=0;d<4;d++)samples.push([a,b,c,d]);
const source=xs=>xs.every(x=>x<2)?1:0;
let mismatch=0,accepted=0;
for(const xs of samples){let got=validate(...xs);if(got!==source(xs))mismatch++;accepted+=got;}
// Additional observations over all bytes in each coordinate with the other three zero.
let byteCoordinateChecks=0;
for(let i=0;i<4;i++)for(let x=0;x<256;x++){let xs=[0,0,0,0];xs[i]=x;if(validate(...xs)!==source(xs))throw new Error('byte coordinate mismatch');byteCoordinateChecks++;}
// All native arguments in the claimed theorem domain are 32-bit words. This control is outside it.
const outside=[2**32,0,0,0];
const outsideDomain={input:outside,nodeResult:validate(...outside),unboundedNatPredicate:source(outside),meaning:'Host i32 argument wrapping; intentionally outside Fin(2^32) theorem domain'};
const mutations=JSON.parse(fs.readFileSync(path.join(dir,'mutations.json'),'utf8')).cases;
const controls={};
for(const [name,array] of Object.entries(mutations)){
  const raw=Buffer.from(array),valid=WebAssembly.validate(raw);
  const row={native_module_valid:valid};
  if(valid){const f=new WebAssembly.Instance(new WebAssembly.Module(raw),{}).exports.validate;
    let diffs=0;for(const xs of samples)if(f(...xs)!==source(xs))diffs++;
    row.sample_mismatches=diffs;row.value_at_2_0_0_0=f(2,0,0,0);}
  controls[name]=row;
}
// Five fresh in-process batch observations after warmup. Each checks the same 256 tuples.
for(let warm=0;warm<10000;warm++)validate(...samples[warm%256]);
const batches=[];let checksum=0;
for(let k=0;k<5;k++){const start=performance.now();let bad=0;
  for(let repeat=0;repeat<1000;repeat++)for(const xs of samples){const got=validate(...xs);checksum+=got;if(got!==source(xs))bad++;}
  const ms=performance.now()-start;if(bad)throw new Error('timed mismatch');batches.push({tuples:256,repetitions:1000,ms,ms_per_256:ms/1000});}
if(mismatch!==0||accepted!==16)throw new Error('positive semantic control failed');
const report={status:'pass',node:process.version,versions:process.versions,nodeExecutable:process.execPath,nodeSha256:crypto.createHash('sha256').update(fs.readFileSync(process.execPath)).digest('hex'),
 moduleSha256:crypto.createHash('sha256').update(bytes).digest('hex'),moduleBytes:bytes.length,imports,exports,
 compileMs,instantiateMs,domain:{tuples:256,each_coordinate:[0,1,2,3],predicate:'each unsigned 32-bit parameter < 2'},mismatch,accepted,byteCoordinateChecks,outsideDomain,controls,batches,checksum,
 boundary:'Observed Node/V8 execution and unverified host harness; complete artifact has independent Lean literal/parser proof. No native machine-code or engine verification.'};
fs.writeFileSync(path.join(dir,'wasm-execution.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify(report));
