# Seiberg–Witten Lean

Lean 4 formalization of N. Seiberg and E. Witten,
[Electric-Magnetic Duality, Monopole Condensation, And Confinement In N=2 Supersymmetric Yang-Mills Theory](https://arxiv.org/abs/hep-th/9407087)
(*Nucl. Phys.* B426 (1994) 19–52, [arXiv:hep-th/9407087](https://arxiv.org/abs/hep-th/9407087)).

Jeromie Beasley · [ORCID](https://orcid.org/0009-0006-4645-5643) · GitHub [dicipler-pixel](https://github.com/dicipler-pixel) · X [@d1c1pler](https://x.com/d1c1pler) · YouTube [@AtlasMemoriae](https://www.youtube.com/@AtlasMemoriae) · [Atlas Memoriae](https://atlas-memoriae.dicipler.workers.dev)

This repo formalizes statements from that 1994 SU(2) paper (no extra matter multiplets; those are a sequel). The source of the theorems is Seiberg and Witten’s paper, as they wrote them.

It is a separate project from [geometric-flux-magnetic-charge-lean](https://github.com/dicipler-pixel/geometric-flux-magnetic-charge-lean) (*From Geometric Flux to Magnetic Charge*). That library is not imported here.

## Paper outline

1. Introduction
2. Review of N=2 SUSY
3. Duality
4. Dyon masses
5. Structure of the moduli space (through §5.6, monopole condensation and confinement)
6. The solution of the model


## Current Lean

- `SeibergWitten/Sources.lean` — paper citation
- `SeibergWitten/Monodromy.lean` — printed §5 monodromies (`T`, `S`, `M_∞`, `M_1`, `M_{-1}`, and the (5.13) conjugation)
- `SeibergWitten/HarmonicChain.lean` — 33 theorems: the charge-lattice monodromy `M(q)`, the pairing/trace identity, continued-fraction neighbor chains, and the algebraic coefficient identities from §6. A literal twin-prime charge lift never gives trace −2. Lean does not prove analytic transport of the periods or physical confinement.

Reproduce the numerical chain table with `python3 scripts/harmonic-chain/check_chains.py`.

## License

Code is MIT. Text is [CC BY 4.0](LICENSE-CC-BY-4.0.md).
