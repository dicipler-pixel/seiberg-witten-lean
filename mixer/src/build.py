# SCRIPT: SW-MIXER-BUILD
# Assembles the single-file mixer: style sheet and 3D parts (3D Mixer Parts v1, as carried inline in the Maxwell mixer),
# the Seiberg-Witten core, and the app. Output file name is versioned; nothing is overwritten.
import sys,re
src=open('/home/claude/mixers/Maxwell_Lean_Mixer_3D_v1.html').read()
css=src[src.index('<style>'):src.index('</style>')+8]
css=css.replace('</style>','.stats b{font-size:15px}\n.stats span,.inst h4{text-transform:none;letter-spacing:.04em}\n.inst{height:126px}\n.kv b{font-size:11px}\n</style>')
parts=src[27362:46412]
assert 'mixer3d_parts_v1' in parts and parts.strip().endswith('</script>')
h0=src.index('/* ---------- number formatting ---------- */'); h1=src.index('/* a cloud of points sampled')
helpers=src[h0:h1]
r0=src.index('/* =====================================================================================================\n   RENDERER'); r1=src.index('/* =====================================================================================================\n   THE FEED OPERATOR')
renderer=src[r0:r1]
core=open('sw_core.js').read(); app=open('sw_app.js').read()
head='''/* SCRIPT: SW-MIXER-APP
   Seiberg and Witten 1994, in Lean — 3D mixer for the repository dicipler-pixel/seiberg-witten-lean (Jeromie Beasley).
   Built on 3D Mixer Parts v1 (Mixer3D helpers). One feed operator (a point u of the moduli space, two loop radii, a charge
   (n_m, n_e) and the mass m) drives every eye. Every readout is recomputed by SWC (core) from the paper's integrals and set
   beside the paper's own statement. */
(function(){
"use strict";
const M = window.Mixer3D, T = M.T, K = window.SWC, $ = id => document.getElementById(id);
const V3 = (x,y,z) => new T.Vector3(x,y,z), v3 = a => new T.Vector3(a[0],a[1],a[2]);
const add = (a,b) => [a[0]+b[0], a[1]+b[1], a[2]+b[2]], sub = (a,b) => [a[0]-b[0], a[1]-b[1], a[2]-b[2]], sm = (s,a) => [s*a[0], s*a[1], s*a[2]], len = a => Math.hypot(a[0],a[1],a[2]);
const still = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
const HEX = { gold:0xf2c14e, cyan:0x63d3ff, rose:0xff6fae, violet:0xb48cff, green:0x63ffb0, grey:0x3a4a5e, ink:0xdfe7ef, faint:0x55657a, red:0xff6b6b, white:0xffffff };
const RGB = h => [((h>>16)&255)/255, ((h>>8)&255)/255, (h&255)/255];

'''
body=open('body.html').read()
html='''<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Seiberg and Witten 1994, in Lean</title>
<meta name="description" content="Interactive 3D mixer for the Lean library seiberg-witten-lean (Jeromie Beasley): the moduli space, the monodromies, the dyon masses and the solution of N = 2 supersymmetric SU(2) Yang-Mills theory, each recomputed beside the statement of Seiberg and Witten's 1994 paper.">
<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Chakra+Petch:wght@500;600&family=Inter+Tight:wght@400;500&family=JetBrains+Mono:wght@400&display=swap">
'''+css+'\n</head><body>\n'+body+'\n<script>\n/* three.js r158 (MIT licence, https://threejs.org), carried inline so that the page runs with no network */\n'+open('t/node_modules/three/build/three.min.js').read().replace('</script>','<\\/script>')+'\n</script>\n'+parts+'\n<script>\n'+core+'\n</script>\n<script>\n'+head+helpers+renderer+app+'\n</script>\n</body></html>\n'
out=sys.argv[1]; open(out,'w').write(html); print(out,len(html))
