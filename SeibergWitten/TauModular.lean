import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
  Seiberg–Witten, hep-th/9407087: how the coupling τ = da_D/da changes when the
  pair (a_D, a) is moved by an integer matrix [[A, B], [C, D]], as in §5.
  The derivatives (da_D, da) are moved by the same matrix, so we work with them
  as complex numbers `x = da_D`, `y = da`, with τ = x / y.
-/

namespace SeibergWitten.Tau

open Complex

/-- New coupling after the pair is moved by [[A,B],[C,D]] is the Möbius image of τ. -/
theorem tau_mobius (A B C D x y : ℂ) (hy : y ≠ 0) (hden : C * (x / y) + D ≠ 0) :
    (A * x + B * y) / (C * x + D * y) = (A * (x / y) + B) / (C * (x / y) + D) := by
  have hden' : C * x + D * y ≠ 0 := by
    intro h; apply hden; field_simp; linear_combination h
  field_simp

/-- S = [[0,1],[-1,0]] sends (a_D, a) to (a, -a_D), so τ ↦ -1/τ. -/
theorem tau_S (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (0 * x + 1 * y) / ((-1) * x + 0 * y) = -1 / (x / y) := by
  rw [show (0:ℂ) * x + 1 * y = y by ring, show (-1:ℂ) * x + 0 * y = -x by ring]
  field_simp

/-- T^b = [[1,b],[0,1]] sends (a_D, a) to (a_D + b a, a), so τ ↦ τ + b. -/
theorem tau_Tb (b : ℤ) (x y : ℂ) (hy : y ≠ 0) :
    (1 * x + (b : ℂ) * y) / (0 * x + 1 * y) = x / y + b := by
  rw [show (0:ℂ) * x + 1 * y = y by ring, show (1:ℂ) * x + (b : ℂ) * y = x + b * y by ring]
  field_simp

/-- P = -I leaves τ unchanged. -/
theorem tau_P (x y : ℂ) :
    ((-1) * x + 0 * y) / (0 * x + (-1) * y) = x / y := by
  rw [show (0:ℂ) * x + (-1) * y = -y by ring, show (-1:ℂ) * x + 0 * y = -x by ring, neg_div_neg_eq]

/-- τ ↦ τ + b keeps Im τ (so Im τ > 0 is kept). -/
theorem im_Tb (τ : ℂ) (b : ℤ) : (τ + b).im = τ.im := by simp

/-- τ ↦ -1/τ keeps Im τ > 0. -/
theorem im_S_pos (τ : ℂ) (h : 0 < τ.im) : 0 < (-1 / τ).im := by
  have hτ : τ ≠ 0 := by rintro rfl; simp at h
  have hn : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτ
  rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, neg_div, neg_neg]
  exact div_pos h hn

/-- The metric Im τ |da|² is unchanged by τ ↦ τ + b (da is unchanged). -/
theorem metric_Tb (τ : ℂ) (b : ℤ) (y : ℂ) :
    (τ + b).im * Complex.normSq y = τ.im * Complex.normSq y := by simp

/-- Under S, da becomes -da_D = -τ da, and Im(-1/τ)|τ da|² = Im τ |da|². -/
theorem metric_S (τ y : ℂ) (hτ : τ ≠ 0) :
    (-1 / τ).im * Complex.normSq (-(τ * y)) = τ.im * Complex.normSq y := by
  have hn : Complex.normSq τ ≠ 0 := by simpa using hτ
  rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, Complex.normSq_neg,
    Complex.normSq_mul]
  field_simp

end SeibergWitten.Tau
