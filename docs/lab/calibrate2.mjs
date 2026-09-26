import { readFileSync } from 'node:fs';
eval(readFileSync(new URL('./models.js', import.meta.url), 'utf8'));
const M = globalThis.LabModels; let best = null;
for (let upd = 2200; upd <= 2320; upd += 10) {
  const m = M.vancouver(upd, 478, 1982), s = M.vancouverStart(); M.vancouverStep(s, m, m.n);
  const d = Math.abs(s.trunc / 1000 - 524.811); if (!best || d < best.d) best = { upd, d, t: s.trunc / 1000, r: s.round / 1000, e: s.exact };
}
console.log(best);
