/* =====================================================================================================
   THE FEED OPERATOR: a point u of the moduli space, the loops, a charge (n_m, n_e) and the mass m
   ===================================================================================================== */
const cx = z => (Math.abs(z[0])<5e-9?0:z[0]).toFixed(4).replace('-','−') + (z[1] < -5e-9 ? ' − ' : ' + ') + Math.abs(z[1]).toFixed(4) + ' i';
const cx3 = z => (Math.abs(z[0])<5e-4?0:z[0]).toFixed(3) + (z[1] < -5e-4 ? '−' : '+') + Math.abs(z[1]).toFixed(3) + 'i';
const cclose = (a,b,tol) => K.abs(K.sub(a,b)) <= (tol||1e-6)*Math.max(1, K.abs(a), K.abs(b));
const matS = N => '[' + N.map(r => r.map(z => { const x = Array.isArray(z) ? z[0] : z; return (Math.abs(x)<5e-7?0:x).toFixed(Number.isInteger(x)?0:4).replace('-','−'); }).join(', ')).join(' ; ') + ']';
const matI = N => '[' + N.map(r => r.map(x => String(x).replace('-','−')).join(', ')).join(' ; ') + ']';
const matClose = (N,Mx) => N.every((r,i) => r.every((z,j) => Math.hypot(z[0]-Mx[i][j], z[1]) < 1e-6));
const rnd = N => N.map(r => r.map(z => Math.round(z[0])));
const U2V = (u,y) => V3(u[0], y||0, -u[1]);
const DEF = { ur:0.6, ui:1.1, r:0.5, R:2.6, nm:1, ne:0, m:0.4 };
const P = Object.assign({ speed:1, playing:!still }, DEF);

/* fixed data: the periods on a grid of the u-plane, and the curve Im(a_D/a) = 0 */
const GN = 61, GS = 3;
const GU = (a,j) => [-GS + 2*GS*a/(GN-1), -GS + 2*GS*j/(GN-1)];
const PG = Array.from({length:GN}, (_,a) => Array.from({length:GN}, (_,j) => K.periods(GU(a,j))));
const MARG_UP = K.marginal(72);
const MARG = MARG_UP.concat(MARG_UP.slice(1,-1).reverse().map(p => [p[0],-p[1]]), [MARG_UP[0]]);
const dyonSign = u => u[1] >= 0 ? 1 : -1;                  /* the dyon that is massless at u = -1 is (1, s) seen from Im u of sign s */
const massDyon = (p,u) => K.mass(p, 1, dyonSign(u));
const excess = (p,u) => { const s = dyonSign(u); return K.mass(p,-s,0) + K.mass(p,s,1) - K.mass(p,0,1); };
const lightMass = (p,u) => Math.min(K.mass(p,1,0), massDyon(p,u));
const lightCol = (p,u,h,k) => { const c = RGB(K.mass(p,1,0) <= massDyon(p,u) ? HEX.rose : HEX.cyan), b = .22 + .78*Math.min(1, h/k); return c.map(x => x*b); };
const GRIDMIN = (() => { let m = 1e9; PG.forEach(r => r.forEach(p => { m = Math.min(m, K.tau(p)[1]); })); return m; })();

function buildFeed(p){ p = p || P; const u = [p.ur, p.ui], pr = K.periods(u), tau = K.tau(pr);
  const one = K.turn([1,0], p.r, Math.PI/2, 540), inf = K.turn([0,0], p.R, Math.PI/2, 720);
  const L1 = K.loop('p1', p.r, true), Lm = K.loop('m1', p.r, true), Li = K.loop('inf', p.R, true);
  return { p:Object.assign({}, p), u, pr, tau, g:K.metric(pr), one, inf, L1, Lm, Li }; }
let F = buildFeed();
const F0 = buildFeed(DEF);     /* the settings at which the readout check is run */

/* shared scenery */
function surf(G, fn, colr, wire){ const s = M.surface(GN, GN, GS, GS); const H = [], C = [];
  for(let a=0;a<GN;a++){ H.push([]); C.push([]); for(let j=0;j<GN;j++){ const h = fn(PG[a][j], GU(a,j)); H[a].push(h); C[a].push(colr(h, PG[a][j], GU(a,j))); } }
  M.setSurface(s, H, C); if(wire != null) s.userData.wire.material.opacity = wire; G.add(s); return s; }
function heightAt(fn, u){ return fn(K.periods(u), u); }
function singMarks(G, y1, ym1, big){ const r = big || .07;
  const a = M.orb(r, HEX.rose); a.position.set(1, y1||0, 0); G.add(a); const b = M.orb(r, HEX.cyan); b.position.set(-1, ym1||0, 0); G.add(b);
  const sa = M.shell(r*3, HEX.rose, .12); sa.position.copy(a.position); G.add(sa); const sb = M.shell(r*3, HEX.cyan, .12); sb.position.copy(b.position); G.add(sb);
  lab(G, 'u = 1', V3(1, (y1||0)+.32, 0), '#ff6fae', .17); lab(G, 'u = −1', V3(-1, (ym1||0)+.32, 0), '#63d3ff', .17); }
function margLine(G, fn, lift, color, op){ const pts = MARG.map(u => U2V(u, (fn ? heightAt(fn,u) : 0) + (lift||0))); const l = M.line(pts, color||HEX.gold, op==null?.95:op); G.add(l); return pts; }
function circlePts(c, r, n, y){ n = n||120; return Array.from({length:n+1}, (_,i) => { const t = 2*Math.PI*i/n; return V3(c[0]+r*Math.cos(t), y||0, -(c[1]+r*Math.sin(t))); }); }
function probeOrb(G, u, y, color){ const o = M.orb(.07, color||HEX.white); o.position.copy(U2V(u,y)); G.add(o); const b = wireBox([.26,.26,.26], HEX.ink, .5); b.position.copy(o.position); G.add(b); return o; }
function axes(G, s, lx, lz){ G.add(segs([[V3(-s,0,0),V3(s,0,0)],[V3(0,0,-s),V3(0,0,s)]], HEX.faint, .55)); lab(G, lx, V3(s+.25,0,0), '#93a3b5', .16); lab(G, lz, V3(0,0,-s-.25), '#93a3b5', .16); }
const ramp = t => M.colour.ramp(t);
/* the transported pair along a turn, drawn as two ribbons above the loop: gold Re a, cyan Re a_D */
function ribbons(G, turn, k){ const ga = turn.pts.map(q => U2V(q.u, k*q.st.a[0])), gd = turn.pts.map(q => U2V(q.u, k*q.st.aD[0]));
  G.add(M.line(turn.pts.map(q => U2V(q.u,0)), HEX.ink, .5)); G.add(M.line(ga, HEX.gold, .95)); G.add(M.line(gd, HEX.cyan, .95));
  const s = turn.pts[0], e = turn.pts[turn.pts.length-1];
  G.add(segs([[U2V(s.u, k*s.st.a[0]), U2V(e.u, k*e.st.a[0])]], HEX.gold, .45)); G.add(segs([[U2V(s.u, k*s.st.aD[0]), U2V(e.u, k*e.st.aD[0])]], HEX.cyan, .45));
  const o1 = M.orb(.06, HEX.gold), o2 = M.orb(.06, HEX.cyan), o0 = M.orb(.045, HEX.white); G.add(o1); G.add(o2); G.add(o0);
  lab(G, 'Re a', U2V(s.u, k*s.st.a[0]+.22), '#f2c14e', .16); lab(G, 'Re a_D', U2V(s.u, k*s.st.aD[0]-.22), '#63d3ff', .16);
  const s1 = streams([ga], 26, .075, HEX.gold), s2 = streams([gd], 26, .075, HEX.cyan); G.add(s1); G.add(s2);
  return { ga, gd, o1, o2, o0, st:[s1,s2], base: turn.pts.map(q => U2V(q.u,0)) }; }
function runRibbon(rb, t){ const n = rb.ga.length-1, x = (((t%1)+1)%1)*n, i = Math.min(n-1, Math.floor(x)), f_ = x-i;
  rb.st.forEach(s => stepStreams(s, .016, .05));
  rb.o1.position.copy(rb.ga[i]).lerp(rb.ga[i+1], f_); rb.o2.position.copy(rb.gd[i]).lerp(rb.gd[i+1], f_); rb.o0.position.copy(rb.base[i]).lerp(rb.base[i+1], f_); }

/* =====================================================================================================
   THE EYES — one per result of the paper, in the paper's order
   ===================================================================================================== */
const EYES = [];
const eye = e => { EYES.push(e); return e; };
const ACTS = [
  ['I', 'The low-energy theory and duality — Sections 2 and 3', ['A','B']],
  ['II', 'Dyon masses — Section 4', ['C','D']],
  ['III', 'Structure of the moduli space — Section 5', ['E','F','G','H','I','J']],
  ['IV', 'The solution of the model — Section 6', ['K','L']]
];
const CHK = rows => rows.filter(r => r[3] === true || r[3] === false);
const NOLEAN = 'not yet formalized';

/* ---------- A. the metric on the moduli space ---------- */
eye({ id:'A', title:'The metric on the moduli space is Im τ |da|², and it is positive', cite:'Sections 2 and 3.1', grades:['P','V'], lean:NOLEAN,
  eq:'ds² = Im τ(a) da dā,   τ = ∂²F/∂a²,   a_D = ∂F/∂a\nds² = Im(da_D dā) = Im[(da_D/du)(dā/dū)] du dū',
  text:'The u-plane, with u = ⟨Tr φ²⟩. The height of the surface is Im τ(u), the inverse squared coupling 4π/g² of the low-energy theory, computed from the solution as τ = (da_D/du)/(da/du). It is positive at every point, as a metric must be; it grows like a logarithm at large |u| and falls to zero only at the two singular points. The white marker is the probe.',
  view:[.6,.5,8.9,.9], uses:['ur','ui'],
  hfn:(p) => 1.5*Math.min(2.2, K.tau(p)[1]),
  make(G){ surf(G, this.hfn, (h,p) => ramp((K.tau(p)[1]-.3)/1.25), .09); singMarks(G, 0, 0); this.dyn = new T.Group(); G.add(this.dyn); },
  calc(F){ const t = F.tau, lhs = F.g, rhs = t[1]*(F.pr.da[0]**2 + F.pr.da[1]**2);
    return [['a(u)', cx(F.pr.a), ''], ['a_D(u)', cx(F.pr.aD), ''], ['τ = (da_D/du)/(da/du)', cx(t), ''], ['Im τ at the probe', f(t[1],6), '> 0', t[1] > 0],
      ['Im[(da_D/du)(dā/dū)]', f(lhs,7), 'Im τ |da/du|² = ' + f(rhs,7), close(lhs,rhs,1e-9)], ['smallest Im τ on the 61 × 61 grid', f(GRIDMIN,6), '> 0', GRIDMIN > 0]]; },
  feed(F){ clear(this.dyn); const y = this.hfn(F.pr); probeOrb(this.dyn, F.u, y+.08); this.dyn.add(segs([[U2V(F.u,0), U2V(F.u,y)]], HEX.ink, .5)); this.R = this.calc(F); },
  step(){ return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- B. duality ---------- */
eye({ id:'B', title:'Duality: S exchanges a and a_D, T shifts a_D, and the metric does not change', cite:'Sections 3.1 and 3.2', grades:['P','V'], lean:NOLEAN,
  eq:'S: (a_D, a) → (a, −a_D),   τ_D = −1/τ\nT_b: a_D → a_D + b a,   τ → τ + b\nds² = −(i/2)(da_D dā − da dā_D)   is invariant under SL(2, R)',
  text:'The upper half-plane of τ. Gold is τ at the probe; cyan is its image −1/τ under S, the coupling of the dual (magnetic) description; rose is τ + 1 under T. The grey curve is the path of τ when u is carried once round the circle |u| = const through the probe: it ends at τ − 2 (violet), which is the action of the monodromy at infinity. The vertical lines and half-circles bound a fundamental domain of the subgroup Γ(2).',
  view:[.3,.72,6.4,.1], uses:['ur','ui'], spin:.3,
  map:t => V3(1.5*t[0], 0, 2.4 - 1.5*Math.min(3.4,t[1])),
  make(G){ const m = this.map; const sc = (c,r) => Array.from({length:49}, (_,i) => m([c + r*Math.cos(Math.PI*i/48), r*Math.sin(Math.PI*i/48)]));
    G.add(M.line([m([-2.4,0]), m([2.4,0])], HEX.ink, .7)); [-1,0,1].forEach(x => G.add(M.line([m([x,0]), m([x,3.4])], HEX.faint, x===0?.25:.6)));
    [-1.5,-.5,.5,1.5].forEach(c => G.add(M.line(sc(c,.5), HEX.faint, .6)));
    lab(G, 'Re τ', m([2.65,0]), '#93a3b5', .16); lab(G, 'Im τ', m([0,3.6]), '#93a3b5', .16); [-2,-1,0,1,2].forEach(x => lab(G, String(x).replace('-','−'), m([x,-.16]), '#5b6b80', .14));
    this.dyn = new T.Group(); G.add(this.dyn); },
  calc(F){ const p = F.pr, t = F.tau, S = {aD:p.a, a:K.sc(-1,p.aD), daD:p.da, da:K.sc(-1,p.daD)}, Tb = K.act([[1,1],[0,1]], p), M1 = K.act(K.M_1, p);
    const tS = K.tau(S), tT = K.tau(Tb), inv = K.div([-1,0], t);
    return [['τ', cx(t), ''], ['τ of the pair (a, −a_D)', cx(tS), '−1/τ = ' + cx(inv), cclose(tS,inv,1e-9)], ['τ of the pair (a_D + a, a)', cx(tT), 'τ + 1 = ' + cx(K.add(t,[1,0])), cclose(tT,K.add(t,[1,0]),1e-9)],
      ['metric after S', f(K.metric(S),8), 'metric before = ' + f(F.g,8), close(K.metric(S),F.g,1e-10)], ['metric after T', f(K.metric(Tb),8), f(F.g,8), close(K.metric(Tb),F.g,1e-10)], ['metric after M₁', f(K.metric(M1),8), f(F.g,8), close(K.metric(M1),F.g,1e-10)]]; },
  feed(F){ clear(this.dyn); this.flow = null; const G = this.dyn, m = this.map, t = F.tau, inv = K.div([-1,0], t);
    const put = (z, color, name, hex) => { const o = M.orb(.1, color); o.position.copy(m(z)).add(V3(0,.03,0)); G.add(o); const sh = M.shell(.24, color, .14); sh.position.copy(o.position); G.add(sh); G.add(rod(m(z), m(z).clone().add(V3(0,.3+.3*Math.min(3,z[1]),0)), color, .016, .75)); lab(G, name, m(z).clone().add(V3(0,.55+.3*Math.min(3,z[1]),0)), hex, .24); };
    const r = Math.max(.3, K.abs(F.u)), th = Math.atan2(F.u[1], F.u[0]);
    if(Math.abs(r-1) > .08){ const tr = K.turn([0,0], r, th, 360); const tp = tr.pts.map(q => m(K.tau(q.st)).add(V3(0,.02,0))); G.add(M.line(tp, HEX.ink, .6)); this.flow = streams([tp], 22, .08, HEX.violet); G.add(this.flow); put(K.tau(tr.st1), HEX.violet, 'τ − 2', '#b48cff'); }
    put(t, HEX.gold, 'τ', '#f2c14e'); put(inv, HEX.cyan, '−1/τ', '#63d3ff'); put(K.add(t,[1,0]), HEX.rose, 'τ + 1', '#ff6fae'); this.R = this.calc(F); },
  step(dt){ if(this.flow) stepStreams(this.flow, dt, .07); return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- C. the BPS mass formula ---------- */
eye({ id:'C', title:'The mass of a dyon: M = √2 |Z|, Z = a n_e + a_D n_m', cite:'Section 4', grades:['P','V'], lean:NOLEAN,
  eq:'M² = 2|Z|²,   Z = a n_e + a_D n_m\nunder a monodromy M:  (a_D, a) → M (a_D, a),   (n_m, n_e) → (n_m, n_e) M⁻¹,   Z unchanged',
  text:'The lattice of charges: the electric charge n_e runs across, the magnetic charge n_m runs in depth. Each column is the value of √2 |a n_e + a_D n_m| at the probe point u. Cyan columns are purely electric charges, rose columns carry magnetic charge, the white column is the charge chosen in the feed, and the gold column is the smallest value on the lattice shown. The formula gives a mass for any charges; it does not by itself say which states exist. Move the probe toward u = 1 and the value for the monopole (1, 0) falls to zero; toward u = −1 it is the value for a dyon.',
  view:[.55,.5,9.8,.5], uses:['ur','ui','nm','ne'],
  make(G){ G.add(M.grid(7,14,0x63d3ff,.06)); lab(G, 'n_e', V3(3.6,0,2.4), '#93a3b5', .17); lab(G, 'n_m', V3(-3.6,0,-2.3), '#93a3b5', .17); this.dyn = new T.Group(); G.add(this.dyn); },
  lightest(p){ let best = null; for(let nm=-2;nm<=2;nm++) for(let ne=-3;ne<=3;ne++){ if(!nm && !ne) continue; if(nm < 0 || (nm === 0 && ne < 0)) continue; const m = K.mass(p,nm,ne); if(!best || m < best.m) best = {nm,ne,m}; } return best; },
  calc(F){ const p = F.pr, nm = F.p.nm, ne = F.p.ne, Z = K.Z(p,nm,ne), N = K.M_INF, q = K.act(N,p), Ni = K.minv(N), w = [nm*Ni[0][0]+ne*Ni[1][0], nm*Ni[0][1]+ne*Ni[1][1]];
    const Z2 = K.Z(q, w[0], w[1]), b = this.lightest(p), sum = K.mass(p,1,0) + K.mass(p,0,1), dy = K.mass(p,1,1);
    return [['Z for (n_m, n_e) = (' + nm + ', ' + ne + ')', cx(Z), 'a n_e + a_D n_m'], ['M = √2 |Z|', f(K.mass(p,nm,ne),6), ''],
      ['Z after M∞, charges (' + w[0] + ', ' + w[1] + ')', cx(Z2), 'unchanged: ' + cx(Z), cclose(Z2,Z,1e-9)],
      ['M(1, 1)', f(dy,6), '≤ M(1, 0) + M(0, 1) = ' + f(sum,6), dy <= sum + 1e-12], ['smallest √2 |Z| on the lattice shown', '(' + b.nm + ', ' + b.ne + ')', '√2 |Z| = ' + f(b.m,6)]]; },
  feed(F){ clear(this.dyn); const G = this.dyn, p = F.pr, b = this.lightest(p);
    for(let nm=-2;nm<=2;nm++) for(let ne=-3;ne<=3;ne++){ if(!nm && !ne){ const o = M.orb(.05, HEX.faint); o.position.set(0,.02,0); G.add(o); continue; }
      const m = K.mass(p,nm,ne), h = 1.9*Math.tanh(m/4.5) + .02, sel = nm === F.p.nm && ne === F.p.ne, lt = Math.abs(m - b.m) < 1e-9;
      G.add(col(ne*.95, -nm*.95, h, sel ? HEX.white : lt ? HEX.gold : nm === 0 ? HEX.cyan : HEX.rose, .26, sel || lt ? 1 : .55)); }
    [-3,-2,-1,0,1,2,3].forEach(n => lab(G, String(n).replace('-','−'), V3(n*.95,-.02,2.45), '#5b6b80', .13)); [-2,-1,0,1,2].forEach(n => lab(G, String(n).replace('-','−'), V3(-3.4,-.02,-n*.95), '#5b6b80', .13)); this.R = this.calc(F); },
  step(){ return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- D. stability ---------- */
eye({ id:'D', title:'A BPS state can decay only where a_D/a is real', cite:'Section 4', grades:['P','V'], lean:NOLEAN,
  eq:'Z = Z₁ + Z₂   ⇒   M ≤ M₁ + M₂\nequality only if Z₁/Z and Z₂/Z are real and positive, which needs  Im(a_D/a) = 0',
  text:'The height of the surface is M₁ + M₂ − M for the decay of the electric state (0, 1) into the two states that become massless at the singular points: the monopole and the dyon. It is positive wherever the triangle inequality is strict, so the decay is forbidden there. It vanishes on the gold curve, where a_D/a is real; the curve passes through u = 1 and u = −1. The paper states the condition; the curve itself is computed here from the solution.',
  view:[.5,.7,8.4,.3], uses:['ur','ui'],
  hfn:(p,u) => 1.5*Math.tanh(1.1*Math.max(0,excess(p,u))),
  make(G){ surf(G, this.hfn, h => ramp(.12 + h/1.5*.8), .06); margLine(G, null, .03, HEX.gold, 1); singMarks(G, 0, 0); this.dyn = new T.Group(); G.add(this.dyn); },
  onCurve(F){ const th = Math.atan2(Math.abs(F.u[1]), F.u[0]); let best = MARG_UP[0], d = 9; MARG_UP.forEach(q => { const t = Math.atan2(q[1], q[0]), e = Math.abs(t-th); if(e < d){ d = e; best = q; } }); return F.u[1] >= 0 ? best : [best[0], -best[1]]; },
  calc(F){ const s = dyonSign(F.u), r = K.div(F.pr.aD, F.pr.a), ex = excess(F.pr, F.u), uc = this.onCurve(F), pc = K.periods(uc), rc = K.div(pc.aD, pc.a), exc = excess(pc, uc);
    const Zs = K.add(K.Z(F.pr,-s,0), K.Z(F.pr,s,1)), Z = K.Z(F.pr,0,1);
    return [['a_D/a at the probe', cx(r), ''], ['Z(' + (-s) + ', 0) + Z(' + s + ', 1)', cx(Zs), 'Z(0, 1) = ' + cx(Z), cclose(Zs,Z,1e-12)], ['M₁ + M₂ − M at the probe', f(ex,7), '≥ 0', ex >= -1e-12],
      ['Im(a_D/a) at u = ' + cx3(uc) + ' on the curve', sci(rc[1]), '0', Math.abs(rc[1]) < 1e-7], ['M₁ + M₂ − M there', sci(exc), '0', Math.abs(exc) < 1e-7], ['the curve crosses the imaginary axis at', '± ' + f(MARG_UP[36][1],6) + ' i', '']]; },
  feed(F){ clear(this.dyn); const y = this.hfn(F.pr, F.u); probeOrb(this.dyn, F.u, y+.08); const uc = this.onCurve(F), o = M.orb(.055, HEX.gold); o.position.copy(U2V(uc,.05)); this.dyn.add(o); this.dyn.add(segs([[U2V(F.u,y+.08), U2V(uc,.05)]], HEX.ink, .35)); this.R = this.calc(F); },
  step(){ return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- E. weak coupling ---------- */
const WEAK = K.turn([0,0], 40, Math.PI/2, 1440);
eye({ id:'E', title:'Weak coupling at large u: the one-loop formulas', cite:'Section 5.1', grades:['P','A','V'], lean:NOLEAN,
  eq:'a ≈ √(2u),   a_D ≈ i (√(2u)/π) ln u      (u → ∞)\nθ_eff = 2π Re τ ≈ −4 arg a',
  text:'The central charges Z/a = n_e + n_m a_D/a at |u| = 40, drawn in the plane: the electric states (cyan) sit on the real axis and do not move; the row of dyons with n_m = 1 (rose) sits at height Im(a_D/a). As u is carried round the circle the row slides to the left, and after one full turn each dyon has taken the place of the one two steps along: the electric charge of a dyon is shifted by −2, which is the effect of the angle θ. The height of each column is the mass in units of |a|.',
  view:[.12,.34,11,.6], uses:[], spin:.2,
  make(G){ G.add(M.line([V3(-4.4,0,0), V3(4.4,0,0)], HEX.ink, .6)); for(let n=-4;n<=4;n++) lab(G, String(n).replace('-','−'), V3(n,-.02,.34), '#5b6b80', .13);
    lab(G, 'Re Z/a', V3(4.9,0,0), '#93a3b5', .16); lab(G, 'Im Z/a', V3(0,0,-2.9), '#93a3b5', .16); this.el = new T.Group(); G.add(this.el);
    for(let n=-4;n<=4;n++){ if(n) this.el.add(col(n, 0, .5*Math.abs(n), HEX.cyan, .22, .85)); }
    this.dy = []; for(let n=-7;n<=9;n++){ const c = col(0,0,1,HEX.rose,.22,.92); G.add(c); const l = M.label('(1, ' + String(n).replace('-','−') + ')', '#ff6fae', .13); G.add(l); this.dy.push({n, c, l}); } this.t = 0;
    this.row = M.line([V3(-4.4,0,0), V3(4.4,0,0)], HEX.rose, .3); G.add(this.row); },
  at(t){ const n = WEAK.pts.length-1, i = Math.min(n, Math.round((((t%1)+1)%1)*n)); return WEAK.pts[i]; },
  calc(F){ const q = WEAK.st0, u = [0,40], su = K.csqrt(K.sc(2,u)), lu = K.clog(u), r1 = K.div(q.a, su), k = K.sub(K.div(K.mul(q.aD,[Math.PI,0]), K.mul(K.I,su)), lu);
    const t = K.tau(q), arga = Math.atan2(q.a[1], q.a[0]), s0 = K.div(WEAK.st0.aD, WEAK.st0.a), s1 = K.div(WEAK.st1.aD, WEAK.st1.a);
    return [['a/√(2u) at u = 40 i', cx(r1), '≈ 1', cclose(r1,[1,0],1e-3)], ['a_D π/(i √(2u)) − ln u', cx(k), 'small beside ln u = ' + f(lu[0],3) + '; here 3 ln 2 − 2 = ' + f(3*Math.log(2)-2,5), ''],
      ['Re τ', f(t[0],5), '≈ −(2/π) arg a = ' + f(-2/Math.PI*arga,5), Math.abs(t[0] + 2/Math.PI*arga) < 5e-3], ['a_D/a after one turn − before', cx(K.sub(s1,s0)), '−2', cclose(K.sub(s1,s0),[-2,0],1e-6)],
      ['matrix of the turn', matS(WEAK.N), 'M∞ = ' + matI(K.M_INF), matClose(WEAK.N, K.M_INF)]]; },
  feed(F){ this.R = this.calc(F); },
  step(dt){ this.t += dt*.06; const q = this.at(this.t), s = K.div(q.st.aD, q.st.a), y = Math.min(2.6, s[1]);
    this.row.position.set(0,0,-y); this.dy.forEach(d => { const x = d.n + s[0], vis = Math.abs(x) < 4.6; d.c.visible = d.l.visible = vis; if(!vis) return; const m = Math.hypot(x, s[1]), h = .5*m; d.c.scale.y = h; d.c.position.set(x, h/2, -y); d.l.position.set(x, h+.2, -y); }); return this.R; },
  check(){ return CHK(this.calc(F0)); } });

/* ---------- F. the monodromy at infinity ---------- */
eye({ id:'F', title:'The monodromy at infinity', cite:'Section 5.1', grades:['P','V'], lean:NOLEAN,
  eq:'u → e^{2πi} u :   a → −a,   a_D → −a_D + 2a\nM∞ = P T⁻² = [−1, 2 ; 0, −1]',
  text:'The pair (a_D, a) is carried once, counter-clockwise, round the circle |u| = R, which encloses both singular points. The gold ribbon is Re a and the cyan ribbon is Re a_D above each point of the circle. Neither ribbon closes: the straight segments join the values at the start and at the end of the turn. The matrix that takes the starting pair to the final pair is read off numerically and set beside the matrix printed in the paper.',
  view:[.7,.5,9.2,.1], uses:['R'],
  make(G){ G.add(M.grid(7,14,0x63d3ff,.06)); singMarks(G, 0, 0); this.dyn = new T.Group(); G.add(this.dyn); this.t = 0; },
  calc(F){ const t = F.inf, s = t.st0, e = t.st1, nm = F.p.nm, ne = F.p.ne, Ni = K.minv(rnd(t.N)), w = [nm*Ni[0][0]+ne*Ni[1][0], nm*Ni[0][1]+ne*Ni[1][1]];
    return [['matrix of the turn', matS(t.N), 'M∞ = ' + matI(K.M_INF), matClose(t.N, K.M_INF)], ['a at the end', cx(e.a), '−a = ' + cx(K.sc(-1,s.a)), cclose(e.a, K.sc(-1,s.a))],
      ['a_D at the end', cx(e.aD), '−a_D + 2a = ' + cx(K.add(K.sc(-1,s.aD), K.sc(2,s.a))), cclose(e.aD, K.add(K.sc(-1,s.aD), K.sc(2,s.a)))],
      ['charges (' + nm + ', ' + ne + ') after the turn', '(' + w[0] + ', ' + w[1] + ')', '(−n_m, −n_e − 2n_m) = (' + (-nm) + ', ' + (-ne-2*nm) + ')', w[0] === -nm && w[1] === -ne-2*nm], ['trace', f(t.N[0][0][0] + t.N[1][1][0],6), '−2', close(t.N[0][0][0] + t.N[1][1][0], -2, 1e-6)]]; },
  feed(F){ clear(this.dyn); this.rb = ribbons(this.dyn, F.inf, .55); this.R = this.calc(F); },
  step(dt){ this.t += dt*.07; if(this.rb) runRibbon(this.rb, this.t); return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- G. the massless monopole ---------- */
eye({ id:'G', title:'At u = 1 a magnetic monopole becomes massless', cite:'Sections 5.3 and 5.4; values from Section 6', grades:['P','V'], lean:NOLEAN,
  eq:'a_D ≈ c₀ (u − 1),   a ≈ a₀ + (i/π) a_D ln a_D\nM₁ = S T² S⁻¹ = [1, 0 ; −2, 1] :   a_D → a_D,   a → a − 2a_D\nc₀ = i/2,   a₀ = 4/π',
  text:'The funnel is the mass √2 |a_D| of the monopole (1, 0), which falls to zero at u = 1. The pair (a_D, a) is carried once round the circle of radius r about u = 1. The cyan ribbon (Re a_D) closes; the gold ribbon (Re a) does not, and the gap is 2a_D: the logarithm in a comes from the loop of the light monopole in the dual, magnetic description, where the theory is weakly coupled.',
  view:[.45,.6,5.6,.35], uses:['r'],
  make(G){ const s = M.surface(41,41,1.1,1.1), H = [], C = []; for(let a=0;a<41;a++){ H.push([]); C.push([]); for(let j=0;j<41;j++){ const u = [1 + 1.1*(a-20)/20, 1.1*(j-20)/20], h = .9*K.mass(K.periods(u),1,0); H[a].push(h); C[a].push(ramp(Math.min(1,h/1.3))); } }
    M.setSurface(s,H,C); s.userData.wire.material.opacity = .07; s.position.set(1,-1.1,0); G.add(s); this.off = V3(0,0,0);
    const o = M.orb(.06, HEX.rose); o.position.set(1,-1.1,0); G.add(o); lab(G, 'massless monopole', V3(1,-1.42,0), '#ff6fae', .15); this.dyn = new T.Group(); G.add(this.dyn); this.t = 0; },
  calc(F){ const t = F.one, s = t.st0, e = t.st1, e3 = [1,1e-3], pe = K.periods(e3), lead = K.mul(K.I, K.sc(.5, K.sub(e3,K.ONE))), p1 = K.periods([1,1e-7]);
    return [['matrix of the turn', matS(t.N), 'M₁ = ' + matI(K.M_1), matClose(t.N, K.M_1)], ['a_D at the end', cx(e.aD), 'a_D = ' + cx(s.aD), cclose(e.aD, s.aD)], ['a at the end', cx(e.a), 'a − 2a_D = ' + cx(K.sub(s.a, K.sc(2,s.aD))), cclose(e.a, K.sub(s.a, K.sc(2,s.aD)))],
      ['a_D at u = 1 + 0.001 i', cx(pe.aD), '≈ i(u − 1)/2 = ' + cx(lead), cclose(K.div(pe.aD,lead), [1,0], 2e-3)], ['a at u = 1', cx(p1.a), '4/π = ' + f(4/Math.PI,5), cclose(p1.a, [4/Math.PI,0], 1e-5)], ['monopole mass √2 |a_D| at u = 1', sci(K.mass(p1,1,0)), '0', K.mass(p1,1,0) < 1e-5]]; },
  feed(F){ clear(this.dyn); const g = new T.Group(); this.dyn.add(g); this.rb = ribbons(g, F.one, .6); this.R = this.calc(F); },
  step(dt){ this.t += dt*.09; if(this.rb) runRibbon(this.rb, this.t); return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- H. the third singularity ---------- */
eye({ id:'H', title:'The third singularity, and the relation M₁ M₋₁ = M∞', cite:'Section 5.5', grades:['P','V'], lean:NOLEAN,
  eq:'M₁ M₋₁ = M∞,   M₋₁ = (TS) T² (TS)⁻¹ = [−1, 2 ; −2, 3]\nM₋₁ = A M₁ A⁻¹,   A = T M₁ = [−1, 1 ; −2, 1]\nthe massless state at u = −1 has charges q with q M₋₁ = q :   q = (1, −1)',
  text:'Three closed paths from one base point: round u = 1 (rose), round u = −1 (cyan), and round both (gold). Beneath them is the smaller of the masses of the monopole and the dyon, rose where it is the monopole and cyan where it is the dyon; it falls to zero under the two singular points. Each carries the pair (a_D, a) back to the base point multiplied by a matrix of integers, found here by transport. With the base point in the lower half-plane the three matrices are the ones printed in the paper, and the path round both points is the product of the other two. The state that becomes massless at u = −1 is a dyon.',
  view:[.45,.52,10.6,-.6], uses:['r','R'],
  make(G){ const under = new T.Group(); under.position.y = -1.7; G.add(under); surf(under, (p,u) => .55*Math.min(3.2, lightMass(p,u)), (h,p,u) => lightCol(p,u,h,1.5), .06); G.add(segs([[V3(1,-1.7,0),V3(1,0,0)],[V3(-1,-1.7,0),V3(-1,0,0)]], HEX.faint, .6)); singMarks(G, 0, 0); const b = M.orb(.07, HEX.white); b.position.copy(U2V([0,-2],0)); G.add(b); lab(G, 'base point', U2V([0,-2],.3), '#dfe7ef', .15); this.dyn = new T.Group(); G.add(this.dyn); },
  legPts(L){ const out = []; L.legs.forEach((g,i) => { const n = i === 1 ? 160 : 24; for(let k=0;k<=n;k++) out.push(U2V(g.U(k/n), .02)); }); return out; },
  calc(F){ const N1 = F.L1.N, Nm = F.Lm.N, Ni = F.Li.N, prod = K.mm(rnd(N1), rnd(Nm)), A = [[-1,1],[-2,1]], Ai = K.minv(A), conjg = K.mm(K.mm(A, K.M_1), Ai), q = [1,-1], R_ = rnd(Nm), qN = [q[0]*R_[0][0]+q[1]*R_[1][0], q[0]*R_[0][1]+q[1]*R_[1][1]];
    const pm = K.periods([-1,-1e-7]), z = K.sub(pm.aD, pm.a);
    return [['path round u = 1', matS(N1), 'M₁ = ' + matI(K.M_1), matClose(N1, K.M_1)], ['path round u = −1', matS(Nm), 'M₋₁ = ' + matI(K.M_M1), matClose(Nm, K.M_M1)], ['path round both', matS(Ni), 'M∞ = ' + matI(K.M_INF), matClose(Ni, K.M_INF)],
      ['product of the first two', matI(prod), 'M∞ = ' + matI(K.M_INF), JSON.stringify(prod) === JSON.stringify(K.M_INF)], ['A M₁ A⁻¹', matI(conjg), 'M₋₁ = ' + matI(K.M_M1), JSON.stringify(conjg) === JSON.stringify(K.M_M1)],
      ['(1, −1) M₋₁', '(' + qN[0] + ', ' + qN[1] + ')', '(1, −1)', qN[0] === 1 && qN[1] === -1], ['Z(1, −1) = a_D − a at u = −1', sci(K.abs(z)), '0', K.abs(z) < 1e-5]]; },
  feed(F){ clear(this.dyn); const G = this.dyn; this.st = [];
    [[F.L1, HEX.rose, 1], [F.Lm, HEX.cyan, 1], [F.Li, HEX.gold, .6]].forEach(([L,c,sp]) => { const pts = this.legPts(L); G.add(M.line(pts, c, .75)); const s = streams([pts], 9, .09, c, true); G.add(s); this.st.push([s, .11*sp]); });
    lab(G, 'M₁', V3(1, .3, -F.p.r-.25), '#ff6fae', .2); lab(G, 'M₋₁', V3(-1, .3, -F.p.r-.25), '#63d3ff', .2); lab(G, 'M∞', V3(0, .3, -F.p.R-.3), '#f2c14e', .2); this.R = this.calc(F); },
  step(dt){ (this.st||[]).forEach(([s,sp]) => stepStreams(s, dt, sp)); return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- I. the symmetry u -> -u ---------- */
eye({ id:'I', title:'The symmetry u → −u of the moduli space', cite:'Sections 2 and 5', grades:['P','V'], lean:NOLEAN,
  eq:'the anomaly breaks U(1)_R to Z₈;  on the u-plane it acts as  u → −u\nds²(−u) = ds²(u),   and the two singular points u = ±1 are exchanged',
  text:'The height of the surface is the metric Im[(da_D/du)(dā/dū)] on the u-plane, which is large near the two singular points and falls off at large |u|. The surface is unchanged by a half-turn about u = 0. The white marker is the probe and the violet marker is its image −u; the two columns are the metric at the two points.',
  view:[.4,.7,8.6,.4], uses:['ur','ui'],
  hfn:(p) => 2.1*Math.tanh(2.2*K.metric(p)),
  make(G){ surf(G, this.hfn, h => ramp(h/2.1), .07); singMarks(G, 0, 0); this.dyn = new T.Group(); G.add(this.dyn); },
  calc(F){ const mu = [-F.u[0], -F.u[1]], cu = [F.u[0], -F.u[1]], g1 = K.metric(K.periods(mu)), g2 = K.metric(K.periods(cu)); let w = 0;
    for(let a=0;a<GN;a++) for(let j=0;j<GN;j++){ const g = K.metric(PG[a][j]), h = K.metric(PG[GN-1-a][GN-1-j]); w = Math.max(w, Math.abs(g-h)/Math.max(1e-9,Math.abs(g))); }
    return [['metric at u', f(F.g,8), ''], ['metric at −u', f(g1,8), f(F.g,8), close(g1, F.g, 1e-8)], ['metric at ū', f(g2,8), f(F.g,8), close(g2, F.g, 1e-8)], ['largest relative difference over the grid', sci(w), '0', w < 1e-8]]; },
  feed(F){ clear(this.dyn); const y = this.hfn(F.pr), mu = [-F.u[0], -F.u[1]]; probeOrb(this.dyn, F.u, y+.08); probeOrb(this.dyn, mu, y+.08, HEX.violet);
    this.dyn.add(rod(U2V(F.u,0), U2V(F.u,y), HEX.white, .014, .8)); this.dyn.add(rod(U2V(mu,0), U2V(mu,y), HEX.violet, .014, .8)); this.dyn.add(segs([[U2V(F.u,y+.08), U2V(mu,y+.08)]], HEX.ink, .35)); this.R = this.calc(F); },
  step(){ return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- J. monopole condensation ---------- */
eye({ id:'J', title:'Breaking to N = 1: the monopoles condense, and electric charge is confined', cite:'Section 5.6', grades:['P','V'], lean:NOLEAN,
  eq:'Ŵ = √2 A_D M M̃ + m U(A_D)\ndŴ = 0 :   √2 M M̃ + m du/da_D = 0,   a_D M = a_D M̃ = 0,   |M| = |M̃|\nM = M̃ = (−m u′(0)/√2)^{1/2}   at a_D = 0',
  text:'A mass term m Tr Φ² is added. Near u = 1 the light fields are the dual photon multiplet A_D and the monopole fields M, M̃. The surface is the size of the first vacuum equation, |√2 M M̃ + m u′(0)|², over the plane of M with M̃ chosen by |M̃| = |M| and the phase that lowers it most. For m = 0 the minimum is at M = 0. For m ≠ 0 it is a circle of radius |M|² = |m u′(0)|/√2 (gold): the monopole field has an expectation value, the magnetic U(1) is broken, and electric charge is confined. The same happens at u = −1 with the dyon, which gives the two vacua of the N = 1 theory.',
  view:[.6,.82,6.0,.3], uses:['m'],
  make(G){ this.s = M.surface(49,49,1.7,1.7); this.s.userData.wire.material.opacity = .07; G.add(this.s); lab(G, 'Re M', V3(1.95,0,0), '#93a3b5', .15); lab(G, 'Im M', V3(0,0,-1.95), '#93a3b5', .15); this.dyn = new T.Group(); G.add(this.dyn); this.t = 0; },
  calc(F){ const p1 = K.periods([1,1e-7]), up = K.div(K.ONE, p1.daD), m = F.p.m, c = m*K.abs(up); let best = 0, bv = 1e99; for(let i=0;i<=40000;i++){ const r2 = i*1e-4, v = (Math.SQRT2*r2 - c)**2; if(v < bv){ bv = v; best = r2; } }
    const MM = K.sc(-m/Math.SQRT2, up), res = K.add(K.sc(Math.SQRT2, MM), K.sc(m, up));
    return [['u′(0) = du/da_D at u = 1', cx(up), '−2i  (from a_D ≈ i(u − 1)/2)', cclose(up, [0,-2], 1e-5)], ['|M|² at the minimum (search)', f(best,4), '|m u′(0)|/√2 = ' + f(c/Math.SQRT2,4), Math.abs(best - c/Math.SQRT2) < 2e-4],
      ['√2 M M̃ + m u′(0) at the vacuum', sci(K.abs(res)), '0', K.abs(res) < 1e-12], ['a_D at the vacuum u = 1', sci(K.abs(p1.aD)), '0', K.abs(p1.aD) < 1e-6], ['monopole condensate', m > 0 ? 'M ≠ 0' : 'M = 0', m > 0 ? 'confinement' : 'no confinement at m = 0']]; },
  feed(F){ clear(this.dyn); const G = this.dyn, c = 2*F.p.m, H = [], C = []; for(let a=0;a<49;a++){ H.push([]); C.push([]); for(let j=0;j<49;j++){ const x = 1.7*(a-24)/24, y = 1.7*(j-24)/24, v = (Math.SQRT2*(x*x+y*y) - c)**2, h = 1.6*Math.tanh(v/1.1); H[a].push(h); C[a].push(ramp(h/1.6)); } }
    M.setSurface(this.s, H, C); this.ring = null;
    if(F.p.m > 0){ const r = Math.sqrt(c/Math.SQRT2), pts = circlePts([0,0], r, 120, .03); G.add(M.line(pts, HEX.gold, 1)); this.ring = streams([pts], 14, .09, HEX.gold, true); G.add(this.ring); lab(G, '⟨M⟩ ≠ 0', V3(r+.1,.35,0), '#f2c14e', .17); }
    else { const o = M.orb(.07, HEX.gold); o.position.set(0,.04,0); G.add(o); lab(G, '⟨M⟩ = 0', V3(0,.35,0), '#f2c14e', .17); } this.R = this.calc(F); },
  step(dt){ if(this.ring) stepStreams(this.ring, dt, .12); return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- K. the curve ---------- */
const offReal = u => [u[0], (u[1] >= 0 ? 1 : -1)*Math.max(.05, Math.abs(u[1]))];
eye({ id:'K', title:'The family of curves y² = (x² − 1)(x − u)', cite:'Section 6', grades:['P','V'], lean:NOLEAN,
  eq:'y² = (x − 1)(x + 1)(x − u)\nλ = (√2/2π) dx √(x − u)/√(x² − 1),   dλ/du = −(√2/4π) dx/y\nτ = (da_D/du)/(da/du) = b₁/b₂,   bᵢ = ∮_{γᵢ} dx/y',
  text:'The plane of x. The surface is ln |y|, which falls at the three branch points x = −1, x = 1 and x = u of the curve. The cyan loop γ₂ goes round the pair −1, 1 and the gold loop γ₁ round the pair 1, u. When the probe u approaches 1 the loop γ₁ shrinks to a point, and when it approaches −1 a loop round −1 and u does: the curve is singular exactly at u = ±1 and at infinity, where its discriminant vanishes. The ratio of the two periods of dx/y is τ, so Im τ > 0 for every u.',
  view:[.5,.75,8.4,-.1], uses:['ur','ui'],
  make(G){ this.s = M.surface(51,51,3,3); this.s.userData.wire.material.opacity = .06; G.add(this.s); this.dyn = new T.Group(); G.add(this.dyn); },
  hx(x, u){ const y2 = K.mul(K.sub(K.mul(x,x),K.ONE), K.sub(x,u)); return .32*Math.max(-4.2, .5*Math.log(K.abs(y2) + 1e-9)); },
  calc(F){ const u = F.u, e = [K.ONE, [-1,0], u], d = (i,j) => K.sub(e[i],e[j]), pr = K.mul(K.mul(d(0,1),d(0,2)), d(1,2)), D = K.mul(pr,pr), Df = K.disc(u);
    const uq = offReal(u), up = [uq[0], Math.abs(uq[1])], pc = K.periods(up), cda = K.contour(up, true), ca = K.contour(up);
    return [['discriminant ∏(eᵢ − eⱼ)²', cx(D), '4(u² − 1)² = ' + cx(Df), cclose(D, Df, 1e-10)], ['|discriminant|', f(K.abs(D),6), 'zero only at u = ±1'],
      ['∮γ₂ λ at u = ' + cx3(up), cx(ca), 'a = ' + cx(pc.a), cclose(ca, pc.a, 1e-7)], ['−(√2/4π) ∮γ₂ dx/y', cx(cda), 'da/du = ' + cx(pc.da), cclose(cda, pc.da, 1e-7)], ['Im τ = Im(b₁/b₂)', f(F.tau[1],6), '> 0', F.tau[1] > 0]]; },
  feed(F){ clear(this.dyn); const G = this.dyn, u = F.u, H = [], C = []; for(let a=0;a<51;a++){ H.push([]); C.push([]); for(let j=0;j<51;j++){ const x = [3*(a-25)/25, 3*(j-25)/25], h = this.hx(x,u); H[a].push(h); C[a].push(ramp(.55 + h/1.6)); } }
    M.setSurface(this.s, H, C);
    [[K.ONE, HEX.rose, 'x = 1'], [[-1,0], HEX.cyan, 'x = −1'], [u, HEX.white, 'x = u']].forEach(([x,c,n]) => { const o = M.orb(.07, c); o.position.copy(U2V(x, .08)); G.add(o); G.add(rod(U2V(x,-1.3), U2V(x,.08), c, .01, .6)); lab(G, n, U2V(x,.42), '#dfe7ef', .15); });
    const ell = (p, q, pad, y) => { const c = K.sc(.5, K.add(p,q)), d = K.sub(q,p), L = K.abs(d)/2 + pad, ang = Math.atan2(d[1], d[0]); return Array.from({length:121}, (_,i) => { const t = 2*Math.PI*i/120, x = L*Math.cos(t), z = pad*Math.sin(t); return U2V([c[0] + x*Math.cos(ang) - z*Math.sin(ang), c[1] + x*Math.sin(ang) + z*Math.cos(ang)], y); }); };
    const g2 = ell([-1,0], [1,0], .34, .3), g1 = ell([1,0], u, .24, .42); G.add(M.line(g2, HEX.cyan, .9)); G.add(M.line(g1, HEX.gold, .9));
    this.st = [streams([g2], 10, .08, HEX.cyan, true), streams([g1], 10, .08, HEX.gold, true)]; this.st.forEach(s => G.add(s)); lab(G, 'γ₂', V3(0,.62,-.5), '#63d3ff', .18); lab(G, 'γ₁', U2V(K.sc(.5,K.add(K.ONE,u)), .78), '#f2c14e', .18); this.R = this.calc(F); },
  step(dt){ (this.st||[]).forEach(s => stepStreams(s, dt, .12)); return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* ---------- L. the solution ---------- */
eye({ id:'L', title:'The solution: a and a_D are periods of λ', cite:'Section 6', grades:['P','V','D'], lean:NOLEAN,
  eq:'a(u) = ∮_{γ₂} λ = (√2/π) ∫₋₁¹ dx √(x − u)/√(x² − 1)\na_D(u) = ∮_{γ₁} λ = (√2/π) ∫₁ᵘ dx √(x − u)/√(x² − 1)\na(1) = 4/π,   a ≈ √(2u) and a_D ≈ i √(2u) ln u/π at large u',
  text:'The two functions over the upper half of the u-plane, drawn on the positive real axis and above it: the gold surface is |a| and the cyan surface is |a_D|. The cyan surface touches zero at u = 1, where the monopole is massless, and the two cross on the curve |a_D| = |a|. The integrals are evaluated here by quadrature, with no other input. The device used in the other panels to carry them along paths, the equation (1 − u²) P″ = P/4, is checked against the integrals in the last row; it is not printed in the paper.',
  view:[.75,.5,8.8,.9], uses:['ur','ui'],
  make(G){ const mk = (fn, color, op) => { const s = M.surface(GN, 31, GS, 1.5), H = [], C = []; for(let a=0;a<GN;a++){ H.push([]); C.push([]); for(let j=0;j<31;j++){ const p = PG[a][30+j], h = .75*fn(p); H[a].push(h); C[a].push(color.map(x => x*(.35 + .65*Math.min(1,h/2)))); } }
      M.setSurface(s,H,C); s.userData.wire.material.opacity = .05; s.children[0].material.opacity = op; s.position.z = -1.5; G.add(s); };
    mk(p => K.abs(p.a), RGB(HEX.gold), .8); mk(p => K.abs(p.aD), RGB(HEX.cyan), .62); singMarks(G, 0, 0); lab(G, '|a|', V3(3.2, .75*K.abs(PG[60][30].a)+.15, 0), '#f2c14e', .18); lab(G, '|a_D|', V3(3.2, .75*K.abs(PG[60][30].aD)-.2, 0), '#63d3ff', .18); this.dyn = new T.Group(); G.add(this.dyn); },
  calc(F){ const uq = offReal(F.u), up = [uq[0], Math.abs(uq[1])], q = K.integrals(up), pc = K.periods(up), p1 = K.periods([1,1e-7]), h = 1e-3;
    const d2 = K.sc(1/(2*h), K.sub(K.integrals([up[0]+h, up[1]]).da, K.integrals([up[0]-h, up[1]]).da)), rhs2 = K.div(K.sc(.25, q.a), K.sub(K.ONE, K.mul(up,up)));
    return [['a by quadrature at u = ' + cx3(up), cx(q.a), 'carried from the base point: ' + cx(pc.a), cclose(q.a, pc.a, 1e-6)], ['a_D by quadrature', cx(q.aD), cx(pc.aD), cclose(q.aD, pc.aD, 1e-6)],
      ['a at u = 1', cx(p1.a), '4/π = ' + f(4/Math.PI,7), cclose(p1.a, [4/Math.PI,0], 1e-5)], ['da_D/du at u = 1', cx(p1.daD), 'i/2', cclose(p1.daD, [0,.5], 1e-5)],
      ['a″ from the integrals', cx(d2), 'a/[4(1 − u²)] = ' + cx(rhs2), cclose(d2, rhs2, 1e-5)]]; },
  feed(F){ clear(this.dyn); const up = [F.u[0], Math.abs(F.u[1])], p = K.periods(up); const o1 = M.orb(.065, HEX.gold); o1.position.copy(U2V(up, .75*K.abs(p.a))); this.dyn.add(o1); const o2 = M.orb(.065, HEX.cyan); o2.position.copy(U2V(up, .75*K.abs(p.aD))); this.dyn.add(o2);
    this.dyn.add(segs([[U2V(up,0), U2V(up, .75*Math.max(K.abs(p.a), K.abs(p.aD)))]], HEX.ink, .5)); this.R = this.calc(F); },
  step(){ return this.R; }, check(){ return CHK(this.calc(F0)); } });

/* =====================================================================================================
   BUILD THE PAGE
   ===================================================================================================== */
const LETTER = {}; EYES.forEach(e => LETTER[e.id] = e);
const GRADE = {P:'stated in the paper', V:'recomputed here', A:'asymptotic statement (≈)', D:'numerical device, not in the paper'};
const GCLS = {P:'g-S', V:'g-V', A:'g-H', D:'g-L'};
const gradeChip = g => `<span class="chip ${GCLS[g]}"><b>${g}</b>${GRADE[g]}</span>`;
function buildPanels(){ const host = $('acts');
  ACTS.forEach(([roman,name,ids]) => { const act = document.createElement('div'); act.className = 'act'; act.innerHTML = `<h3>${roman} · ${name}</h3><div class="grid"></div>`; host.append(act); const grid = act.querySelector('.grid');
    ids.forEach(id => { const e = LETTER[id]; const p = document.createElement('article'); p.className = 'panel'; p.id = 'eye-'+id;
      p.innerHTML = `<div class="ph"><div class="row1"><span class="letter">${id}</span><h4>${e.title}</h4></div>
        <div class="chips"><span class="chip"><b>${e.cite}</b></span>${e.grades.map(gradeChip).join('')}</div><div class="chips"><span class="chip g-O"><b>Lean</b>${e.lean}</span></div>
        <p>${e.text}</p><div class="eqn">${e.eq}</div></div>
        <div class="pv" aria-label="3D view: ${e.title}. Drag to turn, double-click to reset."><div class="vtools"><button data-reset>Reset view</button></div><span class="hint">drag to turn · click then scroll to zoom</span></div>
        <div class="pf"><table class="ro"><thead><tr><th>quantity</th><th>computed</th><th>paper</th></tr></thead><tbody></tbody></table><div class="status" data-status>Readout check not run yet.</div></div>`;
      grid.append(p); const pv = p.querySelector('.pv'); e.view_ = makeView(pv, e.view, {spin:e.spin}); e.tbody = p.querySelector('tbody'); e.status = p.querySelector('[data-status]'); e.panel = p;
      p.querySelector('[data-reset]').onclick = () => { const v = e.view_; v.V.yaw = v.home[0]; v.V.pitch = v.home[1]; v.V.dist = v.home[2]; v.V.ty = v.home[3]||0; v.V.auto = true; };
      e.make(e.view_.G, e.view_); if(e.feed) e.feed(F); }); }); }
function renderRows(e, rows){ if(!rows) return; e.tbody.innerHTML = rows.map(([q,v,pp,ok]) => { const cls = ok === true ? 'hit' : ok === false ? 'miss' : ''; return `<tr><td>${q}</td><td class="${cls}">${v}</td><td class="p">${pp||''}</td></tr>`; }).join(''); }

/* ---------- hero: the u-plane ---------- */
const hero = { mode:'light', dive:0, t:0, anchors:[], st:[] };
const HFN = { light:(p,u) => .8*Math.min(3.2, lightMass(p,u)), coupling:(p) => 1.5*Math.min(2.2, K.tau(p)[1]), monopole:(p) => .62*Math.min(4.2, K.mass(p,1,0)) };
function buildHero(){ const v = makeView($('heroVp'), [.75,.5,26,.4], {fov:38}); hero.v = v; v.spin = .45;
  const star = M.points(1600,.07); for(let i=0;i<1600;i++){ const r = 13+Math.random()*30, t = Math.random()*2*Math.PI, z = Math.acos(2*Math.random()-1); const c = M.colour.ramp(Math.random()).map(x => x*.3);
    M.setPt(star, i, {x:r*Math.sin(z)*Math.cos(t), y:r*Math.cos(z), z:r*Math.sin(z)*Math.sin(t)}, c); } M.flush(star); v.scene.add(star); hero.star = star;
  hero.stat = new T.Group(); v.G.add(hero.stat); hero.dyn = new T.Group(); v.G.add(hero.dyn); v.G.scale.set(1.25,1.25,1.25);
  document.querySelectorAll('#tabs button').forEach(b => b.addEventListener('click', () => { hero.mode = b.dataset.m; document.querySelectorAll('#tabs button').forEach(x => x.setAttribute('aria-pressed', x === b)); heroScene(); heroFeed(); })); }
function heroScene(){ clear(hero.stat); const G = hero.stat, fn = HFN[hero.mode]; hero.st = [];
  surf(G, fn, (h,p,u) => hero.mode === 'light' ? lightCol(p,u,h,2.0) : hero.mode === 'coupling' ? ramp((K.tau(p)[1]-.3)/1.25) : ramp(Math.min(1, h/2.4)), .09);
  const y1 = heightAt(fn,[1,1e-6]), ym = heightAt(fn,[-1,1e-6]); singMarks(G, y1+.06, ym+.06, .09);
  const mp = margLine(G, fn, .04, HEX.gold, 1); const ms = streams([mp], 40, .1, HEX.gold, true); G.add(ms); hero.st.push([ms,.035]);
  [[[1,0],.5,HEX.rose],[[-1,0],.5,HEX.cyan],[[0,0],2.6,HEX.violet]].forEach(([c,r,colr]) => { const pts = Array.from({length:161}, (_,i) => { const t = 2*Math.PI*i/160, u = [c[0]+r*Math.cos(t), c[1]+r*Math.sin(t)]; return U2V(u, heightAt(fn,u)+.05); });
    G.add(M.line(pts, colr, .55)); const s = streams([pts], 12, .1, colr, true); G.add(s); hero.st.push([s,.09]); });
  hero.y1 = y1; hero.ym = ym; hero.ytop = heightAt(fn,[0,.8604]); }
function heroFeed(){ clear(hero.dyn); const fn = HFN[hero.mode], y = fn(F.pr, F.u); probeOrb(hero.dyn, F.u, y+.1); hero.dyn.add(rod(U2V(F.u,y+.1), U2V(F.u,y+1.2), HEX.white, .01, .6));
  const p1 = K.periods([1,1e-7]);
  hero.anchors = [ {p:V3(1, hero.y1+.1, 0), t:'u = 1: massless monopole', s:'a_D = 0 here, so M = √2 |a_D| = 0; monodromy a → a − 2a_D'},
    {p:V3(-1, hero.ym+.1, 0), t:'u = −1: massless dyon', s:'charges (1, −1) with the paper’s matrices; M₁ M₋₁ = M∞'},
    {p:V3(0, hero.ytop+.06, -.8604), t:'curve Im(a_D/a) = 0', s:'the only place where a BPS state can decay (Section 4)'} ];
  if(hero.mode === 'light'){ hero.anchors[0].s = 'rose region: the monopole (1, 0) is lighter than the dyon; its mass √2 |a_D| is zero at this point'; hero.anchors[1].s = 'cyan region: the dyon is the lighter; its mass is zero at this point'; }
  heroStats(); }
function heroStats(){ const p = F.pr, t = F.tau; $('s1').textContent = cx3(p.a); $('s2').textContent = cx3(p.aD); $('s3').textContent = cx3(t); $('s4').textContent = f(K.mass(p,1,0),4); $('s5').textContent = f(massDyon(p,F.u),4); $('s6').textContent = f(t[1],4);
  const inv = K.div([-1,0], t), r = K.div(p.aD, p.a);
  $('i1').innerHTML = `<div>u<b>${cx3(F.u)}</b></div><div>a(u)<b style="color:var(--gold)">${cx3(p.a)}</b></div><div>a_D(u)<b style="color:var(--cyan)">${cx3(p.aD)}</b></div><div>a_D/a<b>${cx3(r)}</b></div>`;
  $('i2').innerHTML = `<div>τ = da_D/da<b>${cx3(t)}</b></div><div>4π/g² = Im τ<b style="color:var(--green)">${f(t[1],4)}</b></div><div>θ_eff = 2π Re τ<b>${f(2*Math.PI*t[0],4)}</b></div><div>dual coupling −1/τ<b>${cx3(inv)}</b></div>`;
  const all = []; for(let nm=0;nm<=2;nm++) for(let ne=-3;ne<=3;ne++){ if(nm === 0 && ne <= 0) continue; all.push([nm,ne,K.mass(p,nm,ne)]); } all.sort((x,y) => x[2]-y[2]);
  $('i3').innerHTML = all.slice(0,4).map((s,i) => `<div>(${s[0]}, ${String(s[1]).replace('-','−')})<b${i?'':' style="color:var(--gold)"'}>${f(s[2],4)}</b></div>`).join('');
  $('i4').innerHTML = `<div>M₁<b>${matI(rnd(F.L1.N))}</b></div><div>M₋₁<b>${matI(rnd(F.Lm.N))}</b></div><div>M₁ M₋₁<b>${matI(K.mm(rnd(F.L1.N), rnd(F.Lm.N)))}</b></div><div>M∞<b style="color:var(--green)">${matI(rnd(F.Li.N))}</b></div>`; }
function heroTick(dt){ const v = hero.v; if(hero.dive < 1){ hero.dive = Math.min(1, hero.dive + (dt||.016)/3.2); const e = 1 - Math.pow(1-hero.dive, 3); v.V.dist = 26 - (26-12.4)*e; }
  hero.t += dt; hero.st.forEach(([s,sp]) => stepStreams(s, dt, sp)); hero.star.rotation.y += dt*.01;
  const host = $('heroVp'), r = host.getBoundingClientRect(), svg = $('leaders'); let html = ''; const cards = document.querySelectorAll('.callout');
  hero.anchors.forEach((a,i) => { const p = a.p.clone(); v.G.localToWorld(p); p.project(v.cam); const x = (p.x+1)/2*r.width, y = (1-p.y)/2*r.height; const c = cards[i]; if(!c) return;
    const ox = [150,-270,-360][i], oy = [70,-30,-150][i]; const cw = c.offsetWidth||230, ch = c.offsetHeight||60; let cxp = Math.max(window.innerWidth > 900 ? r.width*.42 : 10, Math.min(r.width-cw-16, x+ox)), cy = Math.max(80, Math.min(r.height-ch-170, y+oy));
    if(window.innerWidth > 900 && cxp+cw > r.width-430) cy = Math.max(cy, 260); c.style.left = cxp+'px'; c.style.top = cy+'px'; c.innerHTML = `<b>${a.t}</b>${a.s}`; c.style.opacity = p.z < 1 ? 1 : 0;
    const ex = cxp > x ? cxp : cxp + c.offsetWidth, ey = cy+14; const rot = (performance.now()/40)%360;
    html += `<line x1="${x}" y1="${y}" x2="${ex}" y2="${ey}" stroke="#63d3ff" stroke-opacity=".55" stroke-width="1"/><circle cx="${x}" cy="${y}" r="9" fill="none" stroke="#f2c14e" stroke-width="1.2" stroke-dasharray="4 4" transform="rotate(${rot} ${x} ${y})"/><circle cx="${x}" cy="${y}" r="2" fill="#f2c14e"/>`; });
  for(let i=hero.anchors.length;i<cards.length;i++) cards[i].style.opacity = 0;
  svg.innerHTML = html; }

/* =====================================================================================================
   FEED STRIP, CHECK, FILM, CALCULATIONS
   ===================================================================================================== */
function setFeed(){ F = buildFeed(); EYES.forEach(e => { if(e.feed) e.feed(F); }); heroFeed(); buildCalc(); }
function bindStrip(){ const bindR = (id,key,fmt) => { const el = $(id); el.addEventListener('input', () => { P[key] = +el.value; $(id+'o').textContent = fmt ? fmt(+el.value) : el.value; if(key !== 'speed') setFeed(); }); };
  bindR('fur','ur'); bindR('fui','ui'); bindR('fr','r'); bindR('fR','R'); bindR('fnm','nm'); bindR('fne','ne'); bindR('fm','m'); bindR('fsp','speed', v => v+'×');
  $('play').addEventListener('click', () => { P.playing = !P.playing; $('play').textContent = P.playing ? 'Pause' : 'Play'; $('play').setAttribute('aria-pressed', !P.playing); });
  $('play').textContent = P.playing ? 'Pause' : 'Play';
  $('check').addEventListener('click', runCheck); $('clean').addEventListener('click', () => { const on = !document.body.classList.contains('clean'); document.body.classList.toggle('clean', on); $('clean').setAttribute('aria-pressed', on); });
  $('film').addEventListener('click', () => { film.on = !film.on; $('film').setAttribute('aria-pressed', film.on); film.i = -1; film.t = 99; }); }
function runCheck(){ let pass = 0, total = 0; $('checkSummary').textContent = 'checking…';
  setTimeout(() => { EYES.forEach(e => { const rows = e.check(); let ok = 0; rows.forEach(r => { if(r[3]) ok++; }); total += rows.length; pass += ok;
      e.status.className = 'status ' + (ok === rows.length ? 'ok' : 'bad'); e.status.innerHTML = `Readout check: ${ok}/${rows.length} computed values agree with the paper’s. ` + rows.map(r => `${r[0]}: ${r[1]} (paper: ${r[2]})`).join(' · '); });
    $('checkSummary').textContent = `${pass}/${total} computed values agree with the paper’s, ${EYES.length} eyes`; $('checkSummary').className = pass === total ? 'ok' : ''; window.SW_CHECK = {pass,total}; }, 30); }
const film = {on:false, i:-1, t:0};
function filmTick(dt){ if(!film.on) return; film.t += dt; if(film.t < 10) return; film.t = 0; const top0 = film.i >= 0 ? EYES[film.i].panel.offsetTop : -1; do{ film.i = (film.i+1) % EYES.length; }while(EYES[film.i].panel.offsetTop === top0 && film.i !== 0); EYES[film.i].panel.scrollIntoView({behavior:still?'auto':'smooth', block:'center'}); }

function buildCalc(){ const row = (name, N, Mx) => `<tr><td>${name}</td><td>${matS(N)}</td><td class="${matClose(N,Mx)?'hl':'up'}">${matI(Mx)}</td><td>${f(N[0][0][0]+N[1][1][0],4)}</td></tr>`;
  $('tM').innerHTML = row('round u = 1, radius ' + F.p.r, F.L1.N, K.M_1) + row('round u = −1, radius ' + F.p.r, F.Lm.N, K.M_M1) + row('round both, radius ' + F.p.R, F.Li.N, K.M_INF);
  const pr = K.mm(rnd(F.L1.N), rnd(F.Lm.N)), sq1 = K.mm([[0,0],[-2,0]], [[0,0],[-2,0]]);
  $('oM').innerHTML = `product of the first two = <b>${matI(pr)}</b><br>M∞ = <span class="g">${matI(K.M_INF)}</span><br>M₁ − 1 = [0, 0 ; −2, 0],  (M₁ − 1)² = <span class="g">${matI(sq1)}</span><br><span class="d">each matrix has trace ±2 and is not diagonalizable: the logarithm of the one-loop formula</span>`;
  const all = []; for(let nm=0;nm<=2;nm++) for(let ne=-3;ne<=3;ne++){ if(nm === 0 && ne <= 0) continue; const Z = K.Z(F.pr,nm,ne); all.push([nm,ne,Z,Math.SQRT2*K.abs(Z)]); } all.sort((x,y) => x[3]-y[3]);
  $('tS').innerHTML = all.slice(0,8).map((s,i) => `<tr><td>(${s[0]}, ${String(s[1]).replace('-','−')})</td><td>${cx(s[2])}</td><td class="${i?'':'hl'}">${f(s[3],6)}</td></tr>`).join('');
  $('tR').innerHTML = [1.01,1.5,2,5,20,100].map(x => { const p = K.periods([x,1e-9]), t = K.tau(p); return `<tr><td>${x}</td><td>${f(p.a[0],6)}</td><td>${f(Math.sqrt(2*x),6)}</td><td>${f(p.aD[1],6)}</td><td>${f(Math.sqrt(2*x)*Math.log(x)/Math.PI,6)}</td><td>${f(t[1],6)}</td></tr>`; }).join('');
  const p1 = K.periods([1,1e-7]); $('oV').innerHTML = `a(1) = <b>${f(p1.a[0],8)}</b><br>4/π = <span class="g">${f(4/Math.PI,8)}</span><br>da_D/du at u = 1 = <b>${cx(p1.daD)}</b><br>i/2 <span class="d">from a_D ≈ i(u − 1)/2</span><br>curve Im(a_D/a) = 0 on the imaginary axis: u = ± <b>${f(MARG_UP[36][1],6)}</b> i<br>τ at u = 0: <b>${cx(K.tau(K.periods([0,1e-6])))}</b>`; }

/* =====================================================================================================
   GO
   ===================================================================================================== */
buildHero(); heroScene(); buildPanels(); heroFeed(); bindStrip(); buildCalc();
$('share').addEventListener('click', async () => { const url = location.href.split('#')[0]; try{ await navigator.clipboard.writeText(url); $('share').textContent = 'Link copied'; }catch(e){ $('share').textContent = 'Copy the address bar'; } setTimeout(() => $('share').textContent = 'Share', 1800); });
const pastHero = () => document.body.classList.toggle('past', window.scrollY > $('top').offsetHeight-90); window.addEventListener('scroll', pastHero, {passive:true}); pastHero();
let last = performance.now(), readT = 0;
function frame(now){ const raw = Math.max(0, Math.min(.05, (now-last)/1000)); last = now; const dt = P.playing ? raw*P.speed : 0;
  const W = window.innerWidth, H = window.innerHeight; const cv = R.domElement; if(cv.width !== Math.floor(W*R.getPixelRatio()) || cv.height !== Math.floor(H*R.getPixelRatio())) R.setSize(W,H,false);
  R.setScissorTest(false); R.clear(); R.setScissorTest(true); readT += raw; const doRead = readT > .15; if(doRead) readT = 0;
  for(const v of views){ const r = v.el.getBoundingClientRect(); v.visible = r.bottom > 0 && r.top < H && r.width > 0 && r.height > 0; if(!v.visible) continue;
    if(v.V.auto && P.playing && !still) v.V.yaw += raw*.07*(v.spin||1);
    const D = v.V.dist; v.cam.position.set(D*Math.cos(v.V.pitch)*Math.sin(v.V.yaw), v.V.ty + D*Math.sin(v.V.pitch), D*Math.cos(v.V.pitch)*Math.cos(v.V.yaw)); v.cam.lookAt(0, v.V.ty, 0);
    v.cam.aspect = r.width/r.height; if(v === hero.v){ const wide = window.innerWidth > 900; v.cam.setViewOffset(r.width, r.height, wide ? -r.width*.17 : 0, wide ? r.height*.03 : 0, r.width, r.height); } v.cam.updateProjectionMatrix();
    if(v === hero.v) heroTick(dt); else { const e = EYES.find(x => x.view_ === v); const rows = e.step(dt, F, doRead); if(doRead) renderRows(e, rows); }
    R.setViewport(r.left, H-r.bottom, r.width, r.height); R.setScissor(r.left, Math.max(0, H-r.bottom), r.width, r.height); R.render(v.scene, v.cam); }
  filmTick(raw); requestAnimationFrame(frame); }
requestAnimationFrame(frame);
window.MIXER_SW = { EYES, F:() => F, P, setFeed, runCheck, views, hero };
})();
