import fs from 'node:fs';
const bytes=fs.readFileSync(process.argv[2]);const module=await WebAssembly.compile(bytes);const imports=WebAssembly.Module.imports(module);if(imports.length)throw new Error('unexpected imports');
const {exports:s}=await WebAssembly.instantiate(module,{});let cases=0;const start=performance.now();
for(let seed=0;seed<32;seed++)for(let len=0;len<=64;len++)for(const d of [0,1,2,16,63,64,128])for(let mode=0;mode<4;mode++){if(s.check_case(seed,len,d,mode)!==0)throw new Error('packet mismatch');cases++;}
for(let b=0;b<256;b++)for(let i=0;i<4;i++)if(s.invalid_flag(b,i)!==0)throw new Error('flag mismatch');
if(s.check_case(0,65,0,0)!==99 || s.invalid_flag(256,0)!==99)throw new Error('domain mismatch');
console.log(JSON.stringify({cases,flag_controls:1024,out_of_domain:2,all_match:true,layout:Array.from({length:5},(_,i)=>s.layout(i)),imports,runtime_ms:performance.now()-start,wasm_bytes:bytes.length,node:process.version,v8:process.versions.v8}));
