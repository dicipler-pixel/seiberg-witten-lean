/* SCRIPT: SW-MIXER-CORE
   Computational core of the Seiberg-Witten mixer (repository dicipler-pixel/seiberg-witten-lean).
   Source of every formula: N. Seiberg and E. Witten, Nucl. Phys. B426 (1994) 19, hep-th/9407087, in the paper's own
   normalization (singularities at u = 1, u = -1 and infinity; Z = a n_e + a_D n_m; M = sqrt2 |Z|).
   The periods are the paper's integrals (Section 6):
       a(u)   = (sqrt2/pi) Int_{-1}^{1} dx sqrt(x-u)/sqrt(x^2-1)
       a_D(u) = (sqrt2/pi) Int_{1}^{u}  dx sqrt(x-u)/sqrt(x^2-1)
   evaluated by Gauss-Legendre quadrature at a base point and carried to any other u, along any path, by the second-order
   equation both integrals satisfy, (1-u^2) P'' = P/4. That equation is a numerical device here (it is not printed in the
   paper); CHECK rows compare it with the integrals directly. Runs in the browser and in Node. */
(function(root){
"use strict";
const PI=Math.PI, S2=Math.SQRT2;
/* ---------- complex numbers as [re, im] ---------- */
const C=(x,y)=>[x,y||0];
const add=(a,b)=>[a[0]+b[0],a[1]+b[1]], sub=(a,b)=>[a[0]-b[0],a[1]-b[1]];
const mul=(a,b)=>[a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]];
const sc=(s,a)=>[s*a[0],s*a[1]];
const conj=a=>[a[0],-a[1]];
const abs=a=>Math.hypot(a[0],a[1]);
const div=(a,b)=>{ const d=b[0]*b[0]+b[1]*b[1]; return [(a[0]*b[0]+a[1]*b[1])/d,(a[1]*b[0]-a[0]*b[1])/d]; };
const csqrt=a=>{ const r=abs(a); if(r===0) return [0,0]; const x=Math.sqrt((r+Math.abs(a[0]))/2), y=a[1]/(2*x); return a[0]>=0?[x,y]:[Math.abs(y),a[1]>=0?x:-x]; };
const clog=a=>[Math.log(abs(a)),Math.atan2(a[1],a[0])];
const I=[0,1], ONE=[1,0];
/* ---------- Gauss-Legendre nodes ---------- */
function gauss(n){ const x=[],w=[]; for(let i=0;i<n;i++){ let z=Math.cos(PI*(i+.75)/(n+.5)),pp=0; for(let it=0;it<60;it++){ let p1=1,p2=0; for(let j=0;j<n;j++){ const p3=p2; p2=p1; p1=((2*j+1)*z*p2-j*p3)/(j+1); } pp=n*(z*p1-p2)/(z*z-1); const z1=z; z=z1-p1/pp; if(Math.abs(z-z1)<1e-15) break; } x.push(z); w.push(2/((1-z*z)*pp*pp)); } return {x,w}; }
const GL=gauss(96);
function quad(fn,lo,hi){ let s=[0,0]; const h=(hi-lo)/2,m=(hi+lo)/2; for(let i=0;i<GL.x.length;i++){ s=add(s,sc(GL.w[i]*h,fn(m+h*GL.x[i]))); } return s; }
/* ---------- the paper's integrals on the principal sheet (cuts along the real axis to the left of u = 1) ---------- */
function integrals(u){
  const a  = sc(S2/PI, quad(t=>csqrt(sub(u,[Math.cos(t),0])),0,PI));
  const da = sc(S2/(2*PI), quad(t=>div(ONE,csqrt(sub(u,[Math.cos(t),0]))),0,PI));
  const um=sub(u,ONE);
  const aD = mul(mul(I,sc(2*S2/PI,um)), quad(p=>{ const s=Math.sin(p),c=Math.cos(p); return div([c*c,0],csqrt(add([2,0],sc(s*s,um)))); },0,PI/2));
  const daD= mul(I,sc(S2/PI, quad(p=>{ const s=Math.sin(p); return div(ONE,csqrt(add([2,0],sc(s*s,um)))); },0,PI/2)));
  return {a,aD,da,daD}; }
/* ---------- transport along a path u(t), t in [0,1], by (1-u^2) P'' = P/4 (RK4) ---------- */
function rhs(u,y,du){ const k=div([0.25,0],sub(ONE,mul(u,u))); return [mul(y[1],du), mul(mul(k,y[0]),du)]; }
function rkStep(pathU,pathD,t,h,y){ const f=(tt,yy)=>rhs(pathU(tt),yy,pathD(tt));
  const k1=f(t,y), y2=[add(y[0],sc(h/2,k1[0])),add(y[1],sc(h/2,k1[1]))], k2=f(t+h/2,y2), y3=[add(y[0],sc(h/2,k2[0])),add(y[1],sc(h/2,k2[1]))], k3=f(t+h/2,y3), y4=[add(y[0],sc(h,k3[0])),add(y[1],sc(h,k3[1]))], k4=f(t+h,y4);
  return [add(y[0],sc(h/6,add(add(k1[0],sc(2,k2[0])),add(sc(2,k3[0]),k4[0])))), add(y[1],sc(h/6,add(add(k1[1],sc(2,k2[1])),add(sc(2,k3[1]),k4[1]))))]; }
/* state = {a,aD,da,daD}; path = {U(t), D(t)} */
function transport(st,path,n,each){ let ya=[st.a,st.da], yd=[st.aD,st.daD]; const h=1/n;
  for(let i=0;i<n;i++){ ya=rkStep(path.U,path.D,i*h,h,ya); yd=rkStep(path.U,path.D,i*h,h,yd); if(each) each((i+1)*h,{a:ya[0],da:ya[1],aD:yd[0],daD:yd[1]}); }
  return {a:ya[0],da:ya[1],aD:yd[0],daD:yd[1]}; }
const seg=(p,q,grade)=>{ const d=sub(q,p); if(!grade) return {U:t=>add(p,sc(t,d)), D:()=>d};
  /* grade: cluster the steps toward the end point q (used when q is close to a singular point) */
  return {U:t=>add(p,sc(1-Math.pow(1-t,4),d)), D:t=>sc(4*Math.pow(1-t,3),d)}; };
const circ=(c,r,th0,turns)=>({U:t=>add(c,[r*Math.cos(th0+2*PI*turns*t), r*Math.sin(th0+2*PI*turns*t)]), D:t=>sc(2*PI*turns*r,[-Math.sin(th0+2*PI*turns*t), Math.cos(th0+2*PI*turns*t)])});
/* ---------- base point and principal-sheet evaluation ---------- */
const UB=[0,2];                         /* base point u = 2i, in the upper half-plane */
const BASE=integrals(UB);
function periods(u){ /* principal sheet: upper half-plane (and the real axis approached from above); lower half-plane by reflection */
  if(u[1]<0){ const p=periods([u[0],-u[1]]); return {a:conj(p.a), da:conj(p.da), aD:sc(-1,conj(p.aD)), daD:sc(-1,conj(p.daD))}; }
  if(u[1]<1e-9) u=[u[0],1e-9];
  const d1=Math.min(abs(sub(u,ONE)),abs(add(u,ONE))); if(d1<1e-7) u=[u[0],u[1]+1e-7];
  if(abs(u)>6 && u[1]>.5) return integrals(u);              /* far from the cuts the integrals are evaluated directly */
  const near=d1<.25, far=abs(sub(u,UB));
  return transport(BASE, seg(UB,u,near), near?260:Math.max(90,Math.ceil(far*40))); }
const tau=p=>div(p.daD,p.da);
const metric=p=>p.daD[1]*p.da[0]-p.daD[0]*p.da[1];           /* Im( da_D/du * conj(da/du) ) */
const Z=(p,nm,ne)=>add(sc(ne,p.a),sc(nm,p.aD));
const mass=(p,nm,ne)=>S2*abs(Z(p,nm,ne));
/* ---------- monodromy: carry (a_D, a) round a closed path from the base point and read the matrix ---------- */
function matrixFrom(st0,st1){ /* [aD1; a1] = N [aD0; a0], using values and derivatives */
  const det=sub(mul(st0.aD,st0.da),mul(st0.a,st0.daD));
  const row=(v,dv)=>[div(sub(mul(v,st0.da),mul(dv,st0.a)),det), div(sub(mul(dv,st0.aD),mul(v,st0.daD)),det)];
  return [row(st1.aD,st1.daD), row(st1.a,st1.da)]; }
function loop(kind,R,lower){ /* kind: 'inf' (|u| = R about 0), 'p1' (about u = 1), 'm1' (about u = -1); counter-clockwise.
   Base point u = 2i, or u = -2i when lower is set. The matrices printed in the paper are those of the lower base point. */
  const sg=lower?-1:1, ub=[0,2*sg], st0=lower?periods(ub):BASE; let st=st0, legs=[];
  if(kind==='inf'){ const r=R||3; legs=[seg(ub,[0,sg*r]), circ([0,0],r,sg*PI/2,1), seg([0,sg*r],ub)]; }
  else { const c=kind==='p1'?[1,0]:[-1,0], r=R||.5, p=[c[0],sg*r]; legs=[seg(ub,p), circ(c,r,sg*PI/2,1), seg(p,ub)]; }
  const ns=[120,900,120]; legs.forEach((L,i)=>{ st=transport(st,L,ns[i]); });
  return {N:matrixFrom(st0,st), legs, base:ub}; }
/* a full turn on a circle from a given start state; returns the matrix and the states along the way */
function turn(c,r,th0,n){ const u0=add(c,[r*Math.cos(th0),r*Math.sin(th0)]), st0=periods(u0), pts=[{t:0,u:u0,st:st0}]; const P=circ(c,r,th0,1);
  const st1=transport(st0,P,n||720,(t,s)=>pts.push({t,u:P.U(t),st:s})); return {N:matrixFrom(st0,st1), pts, st0, st1}; }
/* the curve Im(a_D/a) = 0: one point on each ray from u = 0 in the upper half-plane; the lower half is its reflection */
function marginal(n){ const out=[]; n=n||72; for(let i=1;i<n;i++){ const th=PI*i/n, g=r=>{ const p=periods([r*Math.cos(th),r*Math.sin(th)]); return div(p.aD,p.a)[1]; };
    let lo=.3, hi=1.8; if(!(g(lo)<0&&g(hi)>0)) continue; for(let k=0;k<44;k++){ const m=(lo+hi)/2; if(g(m)<0) lo=m; else hi=m; } const r=(lo+hi)/2; out.push([r*Math.cos(th),r*Math.sin(th)]); }
  return [[1,0]].concat(out,[[-1,0]]); }
const M_INF=[[-1,2],[0,-1]], M_1=[[1,0],[-2,1]], M_M1=[[-1,2],[-2,3]];
const mm=(A,B)=>[[A[0][0]*B[0][0]+A[0][1]*B[1][0],A[0][0]*B[0][1]+A[0][1]*B[1][1]],[A[1][0]*B[0][0]+A[1][1]*B[1][0],A[1][0]*B[0][1]+A[1][1]*B[1][1]]];
const minv=A=>{ const d=A[0][0]*A[1][1]-A[0][1]*A[1][0]; return [[A[1][1]/d,-A[0][1]/d],[-A[1][0]/d,A[0][0]/d]]; };
const act=(N,p)=>({aD:add(sc(N[0][0],p.aD),sc(N[0][1],p.a)), a:add(sc(N[1][0],p.aD),sc(N[1][1],p.a)), daD:add(sc(N[0][0],p.daD),sc(N[0][1],p.da)), da:add(sc(N[1][0],p.daD),sc(N[1][1],p.da))});
/* ---------- the curve of the solution ---------- */
const disc=u=>{ const d=sub(mul(u,u),ONE); return sc(4,mul(d,d)); };        /* discriminant of (x^2-1)(x-u) */
/* contour integral of lambda = (sqrt2/2pi) sqrt(x-u)/sqrt(x^2-1) dx round the cut [-1,1] (u outside the contour) */
function contour(u,deriv){ const n=600, r=Math.min(1.6,(1+abs(u))/2); let s=[0,0]; const su=csqrt(sc(-1,u));
  for(let i=0;i<n;i++){ const t=2*PI*(i+.5)/n, x=[r*Math.cos(t),r*Math.sin(t)], dx=sc(2*PI*r/n,[-Math.sin(t),Math.cos(t)]);
    /* both roots are single valued on the contour: sqrt(x^2-1) = x sqrt(1-1/x^2), sqrt(x-u) = sqrt(-u) sqrt(1-x/u) (|x| < |u|) */
    const rxu=mul(su,csqrt(sub(ONE,div(x,u)))), rx2=mul(x,csqrt(sub(ONE,div(ONE,mul(x,x)))));
    const g=deriv?div(ONE,mul(rxu,rx2)):div(rxu,rx2); s=add(s,mul(g,dx)); }
  return deriv?sc(-S2/(4*PI),s):sc(S2/(2*PI),s); }
/* the paper's line integrals evaluated directly on the principal sheet (no transport) */
function lineA(u){ return integrals(u).a; }
function lineAD(u){ return integrals(u).aD; }
const api={C,add,sub,mul,sc,conj,abs,div,csqrt,clog,I,ONE,PI,S2,integrals,transport,seg,circ,UB,BASE,periods,tau,metric,Z,mass,matrixFrom,loop,M_INF,M_1,M_M1,mm,minv,act,disc,contour,lineA,lineAD,quad,turn,marginal};
if(typeof module!=='undefined'&&module.exports) module.exports=api; root.SWC=api;
})(typeof window!=='undefined'?window:globalThis);
