import { readFileSync } from 'node:fs';
eval(readFileSync(new URL('./models.js', import.meta.url), 'utf8'));
const M = globalThis.LabModels;
for (const upd of [2200, 2300, 2400, 2500, 3000]) {
  const m = M.vancouver(upd, 478, 1982), s = M.vancouverStart();
  M.vancouverStep(s, m, m.n);
  console.log(upd, 'updates/day:', 'truncated', (s.trunc / 1000).toFixed(3), ' rounded', (s.round / 1000).toFixed(3), ' full', s.exact.toFixed(3));
}
const P = M.patriot;
for (const h of [1, 8, 20, 48, 72, 100]) { const t = h * 36000; const e = P.exactTime(t) - P.choppedTime(t); console.log(`${h} h: computed ${P.choppedTime(t).toFixed(4)} s, error ${e.toFixed(4)} s, gate shift ${Math.round(e * P.gateShiftPerSecond)} m`); }
