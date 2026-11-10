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

## What is proved

48 theorems, all algebra. CI builds every module against Mathlib and rejects `sorry`, `admit`, `native_decide` and new axioms.

| File | Paper | Statements |
|---|---|---|
| `SeibergWitten/Duality.lean` | Section 3 | the metric density `Im[(da_D/du)(dā/dū)]` is unchanged by `SL(2, ℝ)`, by `S` and by `T_b`; `τ_D = −1/τ`; `τ → τ + b`; the density is `Im τ |da/du|²` |
| `SeibergWitten/DyonMass.lean` | Section 4 | `Z = a n_e + a_D n_m`; `M² = 2|Z|²`; `M ≤ M₁ + M₂`; `Z` unchanged when `(a_D, a)` and the charges are transformed together; massless monopole where `a_D = 0`, massless dyon `(1, −1)` where `a_D = a` |
| `SeibergWitten/Monodromy.lean` | Sections 5.1, 5.4, 5.5 | `M₁ M₋₁ = M∞`; `M∞ = P T⁻²`; `M₁ = S T² S⁻¹`; `M₋₁ = (TS) T² (TS)⁻¹`; `A = T M₁`, `M₋₁ = A M₁ A⁻¹`, `A² = −1`; determinants, traces; each monodromy is `±1` plus a matrix of square zero; the charges fixed by `M₁` and by `M₋₁`; the charges at infinity |
| `SeibergWitten/Curve.lean` | Section 6 | the cubic `(x² − 1)(x − u)`; its discriminant `4(u² − 1)²`; singular exactly at `u = ±1`; the symmetry `u → −u` |

Not yet in the library: the functions `a(u)` and `a_D(u)` as integrals, their values and asymptotic forms, `Im τ > 0`, and anything that needs the quantum field theory itself, which can only enter as stated hypotheses.

## License

Code is MIT. Text is [CC BY 4.0](LICENSE-CC-BY-4.0.md).
