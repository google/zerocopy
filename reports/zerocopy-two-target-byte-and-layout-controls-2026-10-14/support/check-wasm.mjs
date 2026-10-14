import fs from 'node:fs';
const bytes = fs.readFileSync(process.argv[2]);
const module = await WebAssembly.compile(bytes);
const imports = WebAssembly.Module.imports(module);
if (imports.length !== 0) throw new Error('Unexpected imports: ' + JSON.stringify(imports));
const {exports: subject} = await WebAssembly.instantiate(module, {});
const start = performance.now();
for (let byte = 0; byte < 256; byte++) {
  const expected = byte <= 1 ? 1 + byte : 0;
  if (subject.validate_bool(byte) !== expected) throw new Error('Boolean mismatch');
}
for (let first = 0; first < 256; first++) {
  for (let second = 0; second < 256; second++) {
    const expected = first <= 1 && second <= 1 ? 1 + 4 * first + 8 * second : 0;
    if (subject.validate_pair(first, second) !== expected) throw new Error('Pair mismatch');
  }
}
if (subject.validate_bool(256) !== 99 || subject.validate_pair(256, 0) !== 99) throw new Error('Out of domain');
if (subject.byte_controls() !== 18) throw new Error('Other byte controls');
const layout = Array.from({length: 7}, (_, i) => subject.layout(i));
console.log(JSON.stringify({bool: 256, pair: 65536, controls: 18, out_of_domain: 2, all_match: true, layout,
  imports, wasm_bytes: bytes.length, case_runtime_ms: performance.now() - start,
  node: process.version, v8: process.versions.v8}));
