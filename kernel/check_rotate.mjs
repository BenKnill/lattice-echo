// Compare the JS rotation (web/lattice.js) with rotation built from the verified kernel, shear by shear.
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
eval(readFileSync(new URL('../web/lattice.js', import.meta.url), 'utf8'));
const L = globalThis.Lattice, deg = +(process.argv[2] || 30), cycles = +(process.argv[3] || 10);
const R = L.rotationTables(deg);
const input = Buffer.concat([R.A, R.B, R.nA, R.nB].map(t => Buffer.from(t)));
const native = execFileSync(new URL('../build/trace_rotate', import.meta.url).pathname, [String(cycles)], { input }).toString().trim().split('\n');
const pts = L.initialPoints(), h = () => createHash('sha256').update(pts).digest('hex'), js = [h()];
for (let k = 0; k < cycles; k++) for (const [f, T] of [[L.shearX, R.A], [L.shearP, R.B], [L.shearX, R.A], [L.shearX, R.nA], [L.shearP, R.nB], [L.shearX, R.nA]]) { f(pts, T); js.push(h()); }
const bad = js.findIndex((x, i) => x !== native[i]);
console.log(bad < 0 ? `ok: all ${js.length} states match rotation built from the verified kernel (${deg} deg, ${cycles} cycles)` : `MISMATCH at state ${bad}`);
console.log(js.slice(6).every((x, i) => i % 6 !== 0 || x === js[0]) ? 'ok: back to the original after every cycle' : 'round trip FAILED');
