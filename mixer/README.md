# 3D mixer

`Seiberg_Witten_Lean_Mixer_3D_v1.html` is a single self-contained page (three.js r158 is carried inline). Open it in a browser.

It is an explorer of Seiberg and Witten, hep-th/9407087, in the paper's normalization: twelve panels in the paper's order, each with a live 3D scene and a readout that sets a value computed from the integrals of Section 6 beside the paper's own statement. The page's "Readout check" passes 52 of 52 at the default feed.

The Lean library contains no theorem yet, and every panel says so. The numbers on the page are recomputations, not proofs.

`src/` holds the numerical core (`sw_core.js`, runs in Node), the app, the page markup, two core test scripts, the build script and the headless-browser check. The build script takes the style sheet and the shared 3D parts from the Maxwell mixer file, so it needs that file to rebuild.
