import Mathlib

/-!
# Section 4: Dyon masses

Seiberg and Witten, hep-th/9407087, Section 4.

A state of magnetic and electric charges `(n_m, n_e)` has central charge `Z = a n_e + a_D n_m`
and, if it is a BPS state, mass `M = √2 |Z|`. Under a monodromy the pair `(a_D, a)` is multiplied by
a matrix `M` and the charges, as a row vector, by `M⁻¹`; `Z` is unchanged.
-/

namespace SeibergWitten

/-- Section 4: the central charge `Z = a n_e + a_D n_m`. -/
def centralCharge (a aD : ℂ) (nm ne : ℤ) : ℂ := a * (ne : ℂ) + aD * (nm : ℂ)

/-- Section 4: the BPS mass `M = √2 |Z|`. -/
noncomputable def bpsMass (a aD : ℂ) (nm ne : ℤ) : ℝ :=
  Real.sqrt 2 * ‖centralCharge a aD nm ne‖

/-- Section 4: `M² = 2 |Z|²`. -/
theorem bpsMass_sq (a aD : ℂ) (nm ne : ℤ) :
    bpsMass a aD nm ne ^ 2 = 2 * ‖centralCharge a aD nm ne‖ ^ 2 := by
  unfold bpsMass
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The mass is not negative. -/
theorem bpsMass_nonneg (a aD : ℂ) (nm ne : ℤ) : 0 ≤ bpsMass a aD nm ne := by
  unfold bpsMass
  exact mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg _)

/-- The central charge is additive in the charges. -/
theorem centralCharge_add (a aD : ℂ) (nm₁ ne₁ nm₂ ne₂ : ℤ) :
    centralCharge a aD (nm₁ + nm₂) (ne₁ + ne₂)
      = centralCharge a aD nm₁ ne₁ + centralCharge a aD nm₂ ne₂ := by
  unfold centralCharge
  push_cast
  ring

/-- Section 4: a state whose charges are the sum of two others is no heavier than the two
together, `M ≤ M₁ + M₂`. -/
theorem bpsMass_add_le (a aD : ℂ) (nm₁ ne₁ nm₂ ne₂ : ℤ) :
    bpsMass a aD (nm₁ + nm₂) (ne₁ + ne₂) ≤ bpsMass a aD nm₁ ne₁ + bpsMass a aD nm₂ ne₂ := by
  unfold bpsMass
  rw [centralCharge_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg 2)

/-- Section 5.3: where `a_D = 0` the monopole `(1, 0)` is massless. -/
theorem bpsMass_monopole_of_aD_eq_zero (a : ℂ) : bpsMass a 0 1 0 = 0 := by
  simp [bpsMass, centralCharge]

/-- Section 5.5: where `a_D = a` the dyon `(1, -1)` is massless. -/
theorem bpsMass_dyon_of_aD_eq_a (a : ℂ) : bpsMass a a 1 (-1) = 0 := by
  simp [bpsMass, centralCharge]

/-- Section 4: `Z` is unchanged when `(a_D, a)` is multiplied by a matrix `[p, q ; r, s]` of
determinant one and the row of charges `(n_m, n_e)` by its inverse `[s, -q ; -r, p]`. Stated in any
commutative ring. -/
theorem centralCharge_invariant {R : Type*} [CommRing R] (p q r s : R) (h : p * s - q * r = 1)
    (aD a nm ne : R) :
    (r * aD + s * a) * (-nm * q + ne * p) + (p * aD + q * a) * (nm * s - ne * r)
      = a * ne + aD * nm := by
  linear_combination (a * ne + aD * nm) * h

end SeibergWitten
