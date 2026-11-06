import fs from 'node:fs';
const bytes = fs.readFileSync(process.argv[2]);
const module = new WebAssembly.Module(bytes);
const imports = WebAssembly.Module.imports(module);
if (imports.length) throw new Error('unexpected imports: ' + JSON.stringify(imports));
const instance = new WebAssembly.Instance(module, {});
console.log(JSON.stringify(Array.from({length:32}, (_, i) => instance.exports.primitive_case(i) >>> 0)));
