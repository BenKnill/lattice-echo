import assert from 'node:assert/strict';
import fs from 'node:fs';
import vm from 'node:vm';
const root=new URL('../',import.meta.url),read=p=>fs.readFileSync(new URL(p,root),'utf8');
function fixture(){
 const nodes=new Map(),listeners={},timers=new Map();let tickId=0;
 const ctx={createImageData:(w,h)=>({data:new Uint8ClampedArray(w*h*4)}),putImageData(){},drawImage(){},getImageData:()=>({data:Uint8ClampedArray.from({length:256*256*4},(_,i)=>(i*17)&255)})};
 const node=(id,tagName='DIV')=>{if(nodes.has(id))return nodes.get(id);const n={id,tagName,textContent:'',style:{},children:[],attributes:{},value:id==='steps'?'100':'',disabled:false,open:false,hidden:false,classList:{add(){}},onclick:null,replaceChildren(){this.children=[]},append(el){this.children.push(el)},setAttribute(k,v){this.attributes[k]=v},getAttribute(k){return this.attributes[k]},getContext:()=>ctx,click(){if(!this.disabled)this.onclick?.({target:this})}};nodes.set(id,n);return n};
 for(const id of ['scene-next','scene-prev','scene-reset','half-next','half-prev','half-reset','scramble','back','stop','reset','full','p-next','p-prev','p-reset','p-full','play'])node(id,'BUTTON');node('steps','INPUT');
 const document={getElementById:node,createElement:tag=>({tagName:tag.toUpperCase(),style:{},setAttribute(){},getContext:()=>ctx}),querySelector:s=>node(s),body:node('body'),documentElement:{requestFullscreen:()=>Promise.resolve()},exitFullscreen:()=>Promise.resolve()};
 const env={console,document,location:{search:'?present=1',hash:''},history:{replaceState:(_x,_y,v)=>env.location.hash=v},URLSearchParams,matchMedia:()=>({matches:false}),setInterval:fn=>{timers.set(++tickId,fn);return tickId},clearInterval:id=>timers.delete(id),addEventListener:(name,fn)=>listeners[name]=fn,Image:class{set src(_v){this.onload?.()}}};env.window=env;
 const key=(k,target='body')=>{let prevented=false;listeners.keydown({key:k,target:node(target),preventDefault(){prevented=true}});return prevented};
 const tick=()=>{for(const fn of [...timers.values()])fn()};
 return {env,node,key,tick,timers};
}
const F=fixture();vm.createContext(F.env);vm.runInContext(read('docs/lattice.js'),F.env);vm.runInContext(read('docs/live.js'),F.env);
const A=F.env.LatticeLive;
assert.equal(A.getState().badL,0);assert.equal(A.getState().distinct,65536);
for(let phase=0;phase<5;phase++){assert.equal(A.getState().phase,phase);const toy=A.toyState();assert.equal(new Set(toy.map(v=>v.x+8*v.p)).size,64);if(phase===4)assert.ok(toy.every(v=>v.x===v.id%8&&v.p===Math.floor(v.id/8)));if(phase<4)F.node('half-next').click();}
F.node('half-prev').click();assert.equal(A.getState().phase,3);F.key('ArrowRight','steps');assert.equal(A.getState().scene,0);
assert.equal(F.key(' ','half-next'),false);F.key('r','half-next');assert.equal(A.getState().phase,0);assert.match(F.node('selected').textContent,/Cell 10/);
F.node('scramble').click();assert.equal(A.getState().dir,1);F.tick();F.node('stop').click();assert.equal(A.getState().dir,0);assert.equal(A.getState().step,2);F.node('back').click();F.tick();assert.equal(A.getState().badL,0);assert.equal(A.getState().step,0);
F.node('reset').click();F.node('scramble').click();for(let j=0;j<50;j++)F.tick();assert.equal(A.getState().step,100);assert.equal(A.getState().dir,0);assert.equal(A.getState().distinct,65536);F.node('back').click();for(let j=0;j<50;j++)F.tick();assert.equal(A.getState().step,0);assert.equal(A.getState().badL,0);assert.ok(A.getState().badF>0&&A.getState().badF<=65536);assert.match(F.node('float-count').textContent,/bins/);assert.match(F.node('exact-count').textContent,/exact coordinate/);
F.node('scramble').click();F.tick();F.node('reset').click();F.tick();assert.equal(A.getState().step,0);assert.equal(F.timers.size,0);
const initial=JSON.stringify(F.env.presentationState());
for(let scene=1;scene<4;scene++){assert.ok(F.key('ArrowRight','scene-next'));for(let j=0;j<50;j++)F.tick();assert.equal(A.getState().scene,scene);assert.equal(F.node('body').attributes['data-scene-index'],String(scene));assert.equal(A.getState().distinct,65536);if(scene>=2){assert.equal(A.getState().step,0);assert.equal(A.getState().badL,0);assert.ok(A.getState().badF>0)}}
for(let scene=2;scene>=0;scene--){assert.ok(F.key('ArrowLeft','scene-next'));for(let j=0;j<50;j++)F.tick();assert.equal(A.getState().scene,scene)}
F.key('ArrowRight','scene-next');F.tick();assert.equal(A.getState().dir,1);F.node('scene-reset').click();F.tick();assert.equal(JSON.stringify(F.env.presentationState()),initial);assert.equal(F.timers.size,0);
console.log('PASS Lattice controller: four scenes forward/back; all five toy phases; focused-button arrows; slider protection; native Space; scramble/pause/back/restart/reset; exact counters; timer cleanup; deterministic presentation reset');
console.log('DOM harness only: browser rendering is not tested');
