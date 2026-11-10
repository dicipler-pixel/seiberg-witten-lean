// SCRIPT: SW-CORE-TEST-02
// Second round of core checks: lower base point reproduces the paper's printed matrices; contour integrals; marginal curve;
// weak-coupling statements; condensate; decay excess.
const K=require('./sw_core.js'); const f=z=>Array.isArray(z)?`(${z[0].toFixed(9)}, ${z[1].toFixed(9)})`:z.toFixed(9);
const R=N=>N.map(r=>r.map(z=>Math.round(z[0]))); const dev=N=>Math.max(...N.flat().map(z=>Math.hypot(z[0]-Math.round(z[0]),z[1])));
for(const lower of [false,true]){ const a=K.loop('p1',.5,lower), b=K.loop('m1',.5,lower), c=K.loop('inf',3,lower);
  console.log(lower?'lower base:':'upper base:','N1',JSON.stringify(R(a.N)),'N-1',JSON.stringify(R(b.N)),'Ninf',JSON.stringify(R(c.N)),' N1.N-1',JSON.stringify(K.mm(R(a.N),R(b.N))),' N-1.N1',JSON.stringify(K.mm(R(b.N),R(a.N))),' max dev from integers',Math.max(dev(a.N),dev(b.N),dev(c.N)).toExponential(1)); }
for(const u of [[2,1],[0,2.5],[-3,.5],[1.5,-2]]){ const p=K.periods(u); console.log('contour a',f(K.contour(u)),' core a',f(p.a),' | contour da',f(K.contour(u,true)),' core da',f(p.da)); }
const mc=K.marginal(72); console.log('marginal points',mc.length,' on imaginary axis r =',mc[Math.floor(mc.length/2)].map(x=>x.toFixed(6)), ' sample',mc.slice(0,4).map(p=>p.map(x=>x.toFixed(3)).join(',')).join(' | '));
for(const [R_,ph] of [[30,1],[200,2],[3000,.5]]){ const u=[R_*Math.cos(ph),R_*Math.sin(ph)], p=K.periods(u), t=K.tau(p); const arga=Math.atan2(p.a[1],p.a[0]);
  console.log('weak: |u|=%s arg u=%s  Re tau=%s  -(2/pi) arg a=%s  Im tau=%s  (ln|u| + 3ln2)/pi=%s', R_,ph,t[0].toFixed(5),(-2/Math.PI*arga).toFixed(5),t[1].toFixed(5),((Math.log(R_)+3*Math.log(2))/Math.PI).toFixed(5)); }
const p1=K.periods([1,1e-7]); console.log('du/da_D at u=1:',f(K.div(K.ONE,p1.daD)));
for(const u of [[0,.5],[.4,1.5],[0,.86034],[-.5,-.3],[2,-1]]){ const p=K.periods(u), s=u[1]>=0?1:-1; const ex=K.mass(p,-s,0)+K.mass(p,s,1)-K.mass(p,0,1); console.log('excess at',u,ex.toExponential(3),' a_D/a',f(K.div(p.aD,p.a))); }
const t0=Date.now(); let n=0; for(let i=0;i<61;i++) for(let j=0;j<31;j++){ K.periods([-3+i*.1,1e-6+j*.1]); n++; } console.log('grid',n,'points in',Date.now()-t0,'ms');
const tr=K.turn([1,0],.5,Math.PI/2,720); console.log('turn about 1 from upper start:',JSON.stringify(R(tr.N)),' about -1:',JSON.stringify(R(K.turn([-1,0],.5,Math.PI/2).N)),' about 0 R=3:',JSON.stringify(R(K.turn([0,0],3,Math.PI/2).N)),' lower start about -1:',JSON.stringify(R(K.turn([-1,0],.5,-Math.PI/2).N)));
