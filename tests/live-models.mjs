import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
const root=new URL('../',import.meta.url),read=p=>fs.readFileSync(new URL(p,root),'utf8');
const sandbox={};vm.runInNewContext(read('docs/lattice.js'),sandbox);const L=sandbox.Lattice;
let cases=0;
const tables=[...[-5,0,.5,2,4,10].map(K=>({name:`K=${K}`,kick:L.kickTable(K)})),{name:'constant255',kick:new Uint8Array(256).fill(255)},{name:'sawtooth',kick:Uint8Array.from({length:256},(_,i)=>(i*151+73)&255)}];
const unique=p=>{const seen=new Uint8Array(65536);for(let i=0;i<p.length;i+=2)seen[p[i]+256*p[i+1]]++;return seen.every(n=>n===1)};
for(const {name,kick} of tables){
 const p=L.initialPoints(),start=p.slice();assert.ok(unique(p));
 // Check both algebraic inverse orders and each independently calculated coordinate.
 L.fwd(p,kick);assert.ok(unique(p));for(let i=0;i<p.length;i+=2){let x=start[i],q=(start[i+1]+kick[x])&255;assert.equal(p[i],(x+q)&255);assert.equal(p[i+1],q)}
 L.bwd(p,kick);assert.deepEqual(p,start);L.bwd(p,kick);L.fwd(p,kick);assert.deepEqual(p,start);
 for(let i=0;i<200;i++)L.fwd(p,kick);assert.ok(unique(p));
 for(let i=0;i<200;i++)L.bwd(p,kick);assert.deepEqual(p,start);
 console.log(`PASS lattice ${name}: 65,536 distinct, exact inverse both orders, 200-step round trip`);cases++;
}
for(const deg of [-85,-30,0,30,85]){const p=L.initialPoints(),start=p.slice(),R=L.rotationTables(deg);for(let j=0;j<10;j++){L.rotate(p,R);assert.ok(unique(p));L.unrotate(p,R);assert.deepEqual(p,start)}cases++;}
const floatStart=L.initialPoints(),xs=Float64Array.from({length:65536},(_,i)=>(floatStart[2*i]+.5)/256),ys=Float64Array.from({length:65536},(_,i)=>(floatStart[2*i+1]+.5)/256),x0=xs.slice(),y0=ys.slice();for(let i=0;i<100;i++)L.floatFwd(xs,ys,2);for(let i=0;i<100;i++)L.floatBwd(xs,ys,2);let bins=0,strict=0;for(let i=0;i<65536;i++){bins+=((Math.floor(xs[i]*256)&255)!==floatStart[2*i]||(Math.floor(ys[i]*256)&255)!==floatStart[2*i+1]);strict+=(xs[i]!==x0[i]||ys[i]!==y0[i]);}assert.ok(strict>bins);console.log(`Float comparison: ${bins} display-bin mismatches, ${strict} strict coordinate mismatches (engine-specific empirical result)`);
console.log('No native kernel execution or proof replay claimed');
