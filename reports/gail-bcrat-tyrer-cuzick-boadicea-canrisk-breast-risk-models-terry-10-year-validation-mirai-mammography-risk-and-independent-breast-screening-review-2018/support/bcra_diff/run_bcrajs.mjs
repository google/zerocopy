// Run the bcra JavaScript port on shared profiles.
// Usage: node run_bcrajs.mjs <path to packages/bcra/src/index.js> <profiles.csv> <out_js.csv>
import { readFileSync, writeFileSync } from 'node:fs';
import { pathToFileURL } from 'node:url';
import { performance } from 'node:perf_hooks';

const [, , indexPath, inCsv, outCsv] = process.argv;
const bcra = await import(pathToFileURL(indexPath).href);
console.log('bcra VERSION', bcra.VERSION);
const lines = readFileSync(inCsv, 'utf8').trim().split(/\r?\n/);
const hdr = lines[0].split(',').map((s) => s.replace(/"/g, ''));
const rows = lines.slice(1).map((l) => {
  // Label is the last column and may contain commas; split the first 11 fields only.
  const parts = l.split(',');
  const o = {};
  hdr.forEach((h, i) => { o[h] = i < hdr.length - 1 ? parts[i] : parts.slice(i).join(','); });
  return o;
});
const num = (x) => Number(x);
const toProfile = (r) => ({
  id: num(r.ID), initialAge: num(r.T1), projectionEndAge: num(r.T2), race: num(r.Race),
  numBreastBiopsies: num(r.N_Biop), ageAtMenarche: num(r.AgeMen), ageAtFirstBirth: num(r.Age1st),
  numRelativesWithBrCa: num(r.N_Rels), atypicalHyperplasia: num(r.HypPlas),
});
const out = ['ID,Success,AbsRisk,AvgRisk,RR1,RR2,BiopsyCat,MenarcheCat,FirstBirthCat,RelCat,HypMult,Errors'];
for (const r of rows) {
  const res = bcra.calculateRisk(toProfile(r), { calculateAverage: true });
  const rv = res.recodedValues || {};
  const errs = (res.validation?.errors || []).join(' | ').replace(/[,\n"]/g, ';');
  const f = (x) => (x === null || x === undefined ? '' : String(x));
  out.push([r.ID, res.success, f(res.absoluteRisk), f(res.averageRisk), f(res.relativeRiskUnder50),
    f(res.relativeRiskAtOrAbove50), f(rv.biopsyCategory), f(rv.menarcheCategory),
    f(rv.firstBirthCategory), f(rv.relativesCategory), f(rv.hyperplasiaMultiplier), errs].join(','));
}
const rnd = rows.filter((r) => r.Set === 'random').map(toProfile);
const t0 = performance.now();
for (const p of rnd) bcra.calculateRisk(p);
const t1 = performance.now();
console.log(`TIMING calculateRisk on random set: n=${rnd.length} elapsed=${((t1 - t0) / 1000).toFixed(3)} s (${((1000 * (t1 - t0)) / rnd.length).toFixed(1)} us/profile)`);
writeFileSync(outCsv, out.join('\n') + '\n');
console.log('wrote', out.length - 1, 'rows');
