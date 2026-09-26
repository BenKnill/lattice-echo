import puppeteer from 'puppeteer-core';
import path from 'node:path'; import { fileURLToPath } from 'node:url'; import fs from 'node:fs';
const here = path.dirname(fileURLToPath(import.meta.url));
const times = fs.readFileSync(path.join(here,'stills.txt'),'utf8').trim().split(',').map(Number);
const b = await puppeteer.launch({ executablePath:'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome', headless:'new', args:['--use-angle=metal','--ignore-gpu-blocklist','--hide-scrollbars','--force-color-profile=srgb','--allow-file-access-from-files'], protocolTimeout: 600000 });
const p = await b.newPage(); await p.setViewport({width:1920,height:1080});
p.on('pageerror', e => console.log('[pageerror]', e.message)); p.on('console', m => console.log('[page]', m.text()));
const t0 = Date.now();
await p.goto('file://'+path.join(here,'film.html'), {waitUntil:'load', timeout: 600000}); await p.evaluate(()=>window.filmReady);
console.log('ready in', ((Date.now()-t0)/1000).toFixed(1), 's');
fs.mkdirSync(path.join(here,'stills'),{recursive:true});
for (const [k,t] of times.entries()) { await p.evaluate(x=>window.renderAt(x), t); await p.screenshot({path: path.join(here,`stills/s${k}.jpg`), type:'jpeg', quality:85}); }
await b.close(); console.log('ok');
