import fs from 'node:fs';
const bytes = fs.readFileSync(process.argv[2]);
const module = new WebAssembly.Module(bytes);
const imports = WebAssembly.Module.imports(module);
if (imports.length !== 0) throw new Error('unexpected imports');
const instance = new WebAssembly.Instance(module, {});
const observed = Array.from({length:12}, (_, index) => instance.exports.aggregate_layout(index));
console.log(JSON.stringify({aggregate:observed,imports,node:process.version,v8:process.versions.v8}));
