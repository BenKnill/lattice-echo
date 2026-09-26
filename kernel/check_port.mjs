// Compare web/lattice.js against the verified machine code, step by step.
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
eval(readFileSync(new URL('../web/lattice.js', import.meta.url), 'utf8'));
const { kickTable, fwd, bwd, initialPoints } = globalThis.Lattice;
const K = +(process.argv[2] || 2.0), steps = +(process.argv[3] || 100);
const kick = kickTable(K);
const native = execFileSync(new URL('../build/trace', import.meta.url).pathname, [String(steps)], { input: Buffer.from(kick) })
  .toString().trim().split('\n');
const pts = initialPoints(), h = () => createHash('sha256').update(pts).digest('hex');
const js = [h()];
for (let s = 0; s < steps; s++) { fwd(pts, kick); js.push(h()); }
for (let s = 0; s < steps; s++) { bwd(pts, kick); js.push(h()); }
const bad = js.findIndex((x, i) => x !== native[i]);
console.log(bad < 0 ? `ok: all ${js.length} states match the verified kernel (K=${K})` : `MISMATCH at state ${bad}`);
console.log(js[0] === js[js.length - 1] ? 'ok: the last state equals the first (exact round trip)' : 'round trip FAILED');
