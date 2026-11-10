// SCRIPT: SW-MIXER-SHOT
// Loads the built page in headless Chrome, reports script errors, runs the page's own readout check, and saves screenshots.
const { chromium } = require('/opt/npm-tools/node_modules/playwright'); const fs=require('fs');
(async()=>{ const file=process.argv[2], tag=process.argv[3]||'d', w=+(process.argv[4]||1440), h=+(process.argv[5]||900);
  const b=await chromium.launch({executablePath:'/usr/bin/google-chrome', args:['--no-sandbox','--use-gl=angle','--use-angle=swiftshader','--enable-unsafe-swiftshader','--ignore-gpu-blocklist']});
  const pg=await b.newPage({viewport:{width:w,height:h}}); const errs=[];
  pg.on('console',m=>{ if(m.type()==='error') errs.push('console: '+m.text()); }); pg.on('pageerror',e=>errs.push('pageerror: '+e.message+'\n'+(e.stack||'').split('\n').slice(0,4).join('\n')));
  await pg.route('**/*', r=>{ const u=r.request().url(); if(u.includes('three.min.js')) return r.fulfill({body:fs.readFileSync('node_modules/three/build/three.min.js','utf8'),contentType:'application/javascript'}); if(u.startsWith('file:')) return r.continue(); return r.abort(); });
  await pg.goto('file://'+file); await pg.waitForTimeout(5000);
  await pg.screenshot({path:`${tag}_hero.png`});
  const res=await pg.evaluate(()=>new Promise(ok=>{ if(!window.MIXER_SW) return ok({err:'no MIXER_SW'}); window.MIXER_SW.runCheck(); setTimeout(()=>{ const bad=[]; window.MIXER_SW.EYES.forEach(e=>e.check().forEach(r=>{ if(!r[3]) bad.push(e.id+': '+r[0]+' = '+r[1]+' | paper '+r[2]); })); ok({chk:window.SW_CHECK,bad,sum:document.getElementById('checkSummary').textContent}); },1500); }));
  console.log(JSON.stringify(res,null,1));
  const ids=await pg.evaluate(()=>window.MIXER_SW?window.MIXER_SW.EYES.map(e=>e.id):[]);
  if(process.argv[6]!=='nopanels') for(const id of ids){ await pg.evaluate(i=>document.getElementById('eye-'+i).scrollIntoView({block:'center'}),id); await pg.waitForTimeout(700); const el=await pg.$('#eye-'+id); await el.screenshot({path:`${tag}_eye_${id}.png`}); }
  await pg.evaluate(()=>document.getElementById('calc').scrollIntoView()); await pg.waitForTimeout(400); await pg.screenshot({path:`${tag}_calc.png`});
  console.log(errs.length?errs.slice(0,12).join('\n'):'no script errors'); await b.close(); })();
