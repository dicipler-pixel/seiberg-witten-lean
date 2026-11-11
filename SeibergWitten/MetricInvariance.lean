import Mathlib

/-!
# Section 3: the metric under SL(2, ℝ)

Seiberg and Witten, hep-th/9407087, Section 3.

The low-energy theory has a metric `ds² = Im τ(a) da dā` with `τ = ∂²F/∂a²` and `a_D = ∂F/∂a`.
In an arbitrary coordinate `u` it is `ds² = Im[(da_D/du)(dā/dū)] du dū` (Section 3.1).
The statements below are the algebraic content of Sections 3.1 and 3.2: the density
`Im[(da_D/du)(dā/dū)]` is unchanged by `SL(2, ℝ)` acting on the pair `(a_D, a)`, and the coupling
`τ = (da_D/du)/(da/du)` gives the density as `Im τ |da/du|²`. The transformations of `τ` itself are in
`TauModular.lean`; what is added here is invariance under every real matrix of determinant one.

Here `daD` and `da` stand for the derivatives `da_D/du` and `da/du` at a point of the `u`-plane.
-/

namespace SeibergWitten.Metric

open Complex

/-- The density of the metric in the coordinate `u`: `Im[(da_D/du)(dā/dū)]` (Section 3.1). -/
noncomputable def metricDensity (daD da : ℂ) : ℝ := (daD * (starRingEnd ℂ) da).im

/-- The density written in real and imaginary parts. -/
theorem metricDensity_eq (daD da : ℂ) :
    metricDensity daD da = daD.im * da.re - daD.re * da.im := by
  simp only [metricDensity, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- Section 3.1: the metric is unchanged when `(a_D, a)` is transformed by a real matrix of
determinant one. -/
theorem metricDensity_sl2 (p q r s : ℝ) (h : p * s - q * r = 1) (daD da : ℂ) :
    metricDensity ((p : ℂ) * daD + (q : ℂ) * da) ((r : ℂ) * daD + (s : ℂ) * da)
      = metricDensity daD da := by
  simp only [metricDensity_eq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (daD.im * da.re - daD.re * da.im) * h

/-- Section 3.2: the metric is unchanged by `S : (a_D, a) → (a, -a_D)`. -/
theorem metricDensity_S (daD da : ℂ) : metricDensity da (-daD) = metricDensity daD da := by
  simp only [metricDensity_eq, Complex.neg_re, Complex.neg_im]
  ring

/-- Section 3.2: the metric is unchanged by `T_b : a_D → a_D + b a`, `b` real. -/
theorem metricDensity_T (b : ℝ) (daD da : ℂ) :
    metricDensity (daD + (b : ℂ) * da) da = metricDensity daD da := by
  simp only [metricDensity_eq, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The coupling `τ = (da_D/du)/(da/du)` (Sections 3.1 and 6). -/
noncomputable def coupling (daD da : ℂ) : ℂ := daD / da

/-- The metric density is `Im τ |da/du|²`, so it is positive exactly when `Im τ > 0`. -/
theorem metricDensity_eq_im_coupling (daD da : ℂ) (h : da ≠ 0) :
    metricDensity daD da = (coupling daD da).im * Complex.normSq da := by
  have hn : Complex.normSq da ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using h
  have key : daD = coupling daD da * da := by
    unfold coupling
    field_simp
  have : metricDensity (coupling daD da * da) da = (coupling daD da).im * Complex.normSq da := by
    simp only [metricDensity_eq, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
    ring
  rw [← key] at this
  exact this

end SeibergWitten.Metric
