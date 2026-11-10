import Mathlib

/-!
# Section 6: The curve

Seiberg and Witten, hep-th/9407087, Section 6.

The solution is given by the family of curves `y² = (x - 1)(x + 1)(x - u)`. The statements here
are the algebra of the cubic: its expanded form, its discriminant `4 (u² - 1)²`, and the fact that
the curve is singular exactly at `u = 1` and `u = -1`.
-/

namespace SeibergWitten

/-- Section 6: the cubic `(x - 1)(x + 1)(x - u) = (x² - 1)(x - u)`. -/
def cubic {R : Type*} [CommRing R] (u x : R) : R := (x - 1) * (x + 1) * (x - u)

theorem cubic_eq {R : Type*} [CommRing R] (u x : R) : cubic u x = (x ^ 2 - 1) * (x - u) := by
  unfold cubic; ring

theorem cubic_expand {R : Type*} [CommRing R] (u x : R) :
    cubic u x = x ^ 3 - u * x ^ 2 - x + u := by
  unfold cubic; ring

/-- The discriminant of the cubic: the squared product of the differences of its roots
`1`, `-1` and `u`. -/
def cubicDisc {R : Type*} [CommRing R] (u : R) : R := ((1 - (-1)) * (1 - u) * (-1 - u)) ^ 2

theorem cubicDisc_eq {R : Type*} [CommRing R] (u : R) : cubicDisc u = 4 * (u ^ 2 - 1) ^ 2 := by
  unfold cubicDisc; ring

/-- Section 6: the curve is singular exactly at `u = 1` and `u = -1`. -/
theorem cubicDisc_eq_zero_iff (u : ℂ) : cubicDisc u = 0 ↔ u = 1 ∨ u = -1 := by
  have h : cubicDisc u = 4 * ((u - 1) * (u + 1)) ^ 2 := by
    unfold cubicDisc; ring
  rw [h]
  constructor
  · intro h0
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    have h1 : ((u - 1) * (u + 1)) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact absurd h' h4
      · exact h'
    have h2 : (u - 1) * (u + 1) = 0 := by
      rcases pow_eq_zero_iff (two_ne_zero) |>.mp h1 with h'
      exact h'
    rcases mul_eq_zero.mp h2 with h' | h'
    · left; exact sub_eq_zero.mp h'
    · right; exact eq_neg_of_add_eq_zero_left h'
  · rintro (h' | h')
    · subst h'; ring
    · subst h'; ring

/-- Section 6: the symmetry `u → -u` of the family: `cubic (-u) (-x) = -cubic u x`. -/
theorem cubic_neg {R : Type*} [CommRing R] (u x : R) : cubic (-u) (-x) = -cubic u x := by
  unfold cubic; ring

/-- The discriminant is unchanged by `u → -u`. -/
theorem cubicDisc_neg {R : Type*} [CommRing R] (u : R) : cubicDisc (-u) = cubicDisc u := by
  unfold cubicDisc; ring

end SeibergWitten
