// SCRIPT: SW-CORE-TEST-01
// Checks the core against the paper's own printed values before any eye is built. A failure here means the eye would lie.
const K=require('./sw_core.js'); const f=(z)=>Array.isArray(z)?`(${z[0].toFixed(10)}, ${z[1].toFixed(10)})`:z.toFixed(10);
const fm=N=>N.map(r=>r.map(z=>`${z[0].toFixed(7)}${z[1]>=0?'+':''}${z[1].toFixed(7)}i`).join('  ')).join(' | ');
// 1. transport against direct integrals at several upper-half-plane points
let w=0; for(const u of [[3,1],[-2.5,.7],[.3,1.2],[0,.4],[1.4,.2],[-1.3,.15],[5,3]]){ const p=K.periods(u), q=K.integrals(u); w=Math.max(w,K.abs(K.sub(p.a,q.a)),K.abs(K.sub(p.aD,q.aD)),K.abs(K.sub(p.da,q.da)),K.abs(K.sub(p.daD,q.daD))); }
console.log('1 transport vs integrals, worst abs diff:',w.toExponential(2));
// 2. a(1) = 4/pi ; a_D near 1 ~ i(u-1)/2
const p1=K.periods([1,1e-7]); console.log('2 a(1) =',f(p1.a),' 4/pi =',(4/Math.PI).toFixed(10),'  a_D(1) =',f(p1.aD),' da_D/du(1) =',f(p1.daD),' (paper: i/2)');
// 3. large u
for(const U of [1e2,1e4,1e6]){ const p=K.integrals([U,1e-9]); console.log('3 u=%s  a/sqrt(2u) = %s   a_D/(i sqrt(2u) ln u/pi) = %s',U,(p.a[0]/Math.sqrt(2*U)).toFixed(8),(p.aD[1]/(Math.sqrt(2*U)*Math.log(U)/Math.PI)).toFixed(6)); }
// 4. monodromies
for(const k of ['inf','p1','m1']) console.log('4',k,fm(K.loop(k).N));
const r=K.loop('p1').N.map(r=>r.map(z=>Math.round(z[0]))), s=K.loop('m1').N.map(r=>r.map(z=>Math.round(z[0]))), t=K.loop('inf').N.map(r=>r.map(z=>Math.round(z[0])));
console.log('  N1 N-1 =',JSON.stringify(K.mm(r,s)),' N-1 N1 =',JSON.stringify(K.mm(s,r)),' Ninf =',JSON.stringify(t));
// 5. Im tau > 0 and metric on a grid; symmetry u -> -u, u -> conj u
let mn=1e9,sym=0; for(let x=-3;x<=3;x+=.25) for(let y=.05;y<=3;y+=.25){ const p=K.periods([x,y]), q=K.periods([-x,-y]); mn=Math.min(mn,K.tau(p)[1]); sym=Math.max(sym,Math.abs(K.metric(p)-K.metric(q))/Math.max(1e-9,Math.abs(K.metric(p)))); }
console.log('5 min Im tau on grid:',mn.toFixed(6),'  worst relative |g(u)-g(-u)|:',sym.toExponential(2));
// 6. which charge is massless at u=-1 from above / below
for(const u of [[-1,1e-6],[-1,-1e-6]]){ const p=K.periods(u); console.log('6 u=',u,' a =',f(p.a),' a_D =',f(p.aD),' a_D - a:',f(K.sub(p.aD,p.a)),' a_D + a:',f(K.add(p.aD,p.a))); }
// 7. contour integral of lambda vs a
for(const u of [[2,1],[0,2.5],[-3,.5]]){ console.log('7 contour:',f(K.contourA(u)),' a:',f(K.periods(u).a)); }
// 8. tau at a few points
for(const u of [[0,1e-6],[0,1],[3,0.0001],[1,.05],[-1,.05]]) console.log('8 u=',u,' tau =',f(K.tau(K.periods(u))),' a_D/a =',f(K.div(K.periods(u).aD,K.periods(u).a)));
