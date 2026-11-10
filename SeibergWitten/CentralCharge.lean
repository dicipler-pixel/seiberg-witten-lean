/-
Seiberg and Witten, hep-th/9407087, Sections 4 and 5: the central charge with the
paper's complex periods `a` and `a_D`.

A state of magnetic charge `n_m` and electric charge `n_e` has `Z = n_m a_D + n_e a`,
and mass `M = √2 |Z|`. Going around a singularity of the `u`-plane changes the column
`(a_D, a)` by a monodromy matrix; the charges then change by the same matrix acting
on the row `(n_m, n_e)`.

Algebra only: `a` and `a_D` are arbitrary complex numbers here. Nothing is said about
the period integrals that give them as functions of `u`.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination

namespace SeibergWitten.CentralCharge

/-- `Z = n_m a_D + n_e a`. -/
def Z (nm ne : ℤ) (aD a : ℂ) : ℂ := (nm : ℂ) * aD + (ne : ℂ) * a

/-- The BPS mass `√2 |Z|`. -/
noncomputable def mass (nm ne : ℤ) (aD a : ℂ) : ℝ := Real.sqrt 2 * ‖Z nm ne aD a‖

/-- A matrix `[[p, q], [r, s]]` acting on the periods: `(a_D, a) ↦ (p a_D + q a, r a_D + s a)`,
written as `Z` evaluated at the new periods. It is `Z` at the old periods with the charges
moved to the row `(n_m, n_e) [[p, q], [r, s]]`. -/
theorem Z_act (p q r s nm ne : ℤ) (aD a : ℂ) :
    Z nm ne (p * aD + q * a) (r * aD + s * a) = Z (nm * p + ne * r) (nm * q + ne * s) aD a := by
  unfold Z; push_cast; ring

/-- For a matrix of determinant one, moving the periods by it and the charges by its inverse
leaves `Z` unchanged. -/
theorem Z_invariant (p q r s nm ne : ℤ) (h : p * s - q * r = 1) (aD a : ℂ) :
    Z (nm * s - ne * r) (ne * p - nm * q) (p * aD + q * a) (r * aD + s * a) = Z nm ne aD a := by
  have h' : ((p : ℂ) * s - q * r) = 1 := by exact_mod_cast h
  unfold Z; push_cast
  linear_combination ((nm : ℂ) * aD + (ne : ℂ) * a) * h'

/-- So the mass is unchanged too. -/
theorem mass_invariant (p q r s nm ne : ℤ) (h : p * s - q * r = 1) (aD a : ℂ) :
    mass (nm * s - ne * r) (ne * p - nm * q) (p * aD + q * a) (r * aD + s * a) = mass nm ne aD a := by
  unfold mass; rw [Z_invariant p q r s nm ne h]

/-- `M² = 2 |Z|²`. -/
theorem mass_sq (nm ne : ℤ) (aD a : ℂ) : mass nm ne aD a ^ 2 = 2 * ‖Z nm ne aD a‖ ^ 2 := by
  unfold mass; rw [mul_pow, Real.sq_sqrt (by norm_num)]

/-! ### The paper's three monodromies acting on the complex periods -/

/-- `M_∞ = [[-1, 2], [0, -1]]`. -/
def actInf (aD a : ℂ) : ℂ × ℂ := (-aD + 2 * a, -a)
/-- `M_1 = [[1, 0], [-2, 1]]`. -/
def act1 (aD a : ℂ) : ℂ × ℂ := (aD, -2 * aD + a)
/-- `M_{-1} = [[-1, 2], [-2, 3]]`. -/
def actNeg1 (aD a : ℂ) : ℂ × ℂ := (-aD + 2 * a, -2 * aD + 3 * a)

/-- `M_1 M_{-1} = M_∞` on the periods: going around `u = -1` and then `u = 1` is going
around `u = ∞`. -/
theorem act1_actNeg1 (aD a : ℂ) :
    act1 (actNeg1 aD a).1 (actNeg1 aD a).2 = actInf aD a := by
  unfold act1 actNeg1 actInf; ext <;> simp; ring

/-- Around `u = 1` the monopole `(1, 0)` keeps `Z = a_D`. -/
theorem monopole_Z_M1 (aD a : ℂ) : Z 1 0 (act1 aD a).1 (act1 aD a).2 = Z 1 0 aD a := by
  unfold Z act1; push_cast; ring

/-- Around `u = -1` the dyon `(1, -1)` keeps `Z = a_D - a`. -/
theorem dyon_Z_Mneg1 (aD a : ℂ) : Z 1 (-1) (actNeg1 aD a).1 (actNeg1 aD a).2 = Z 1 (-1) aD a := by
  unfold Z actNeg1; push_cast; ring

/-- Around `u = ∞` the W boson `(0, 1)` has `Z ↦ -Z`, so its mass is unchanged. -/
theorem W_Z_Minf (aD a : ℂ) : Z 0 1 (actInf aD a).1 (actInf aD a).2 = -Z 0 1 aD a := by
  unfold Z actInf; push_cast; ring

theorem W_mass_Minf (aD a : ℂ) : mass 0 1 (actInf aD a).1 (actInf aD a).2 = mass 0 1 aD a := by
  unfold mass; rw [W_Z_Minf, norm_neg]

/-- Around `u = ∞` a general state has `Z_{(n_m, n_e)} ↦ Z_{(-n_m, 2 n_m - n_e)}`. -/
theorem Z_Minf (nm ne : ℤ) (aD a : ℂ) :
    Z nm ne (actInf aD a).1 (actInf aD a).2 = Z (-nm) (2 * nm - ne) aD a := by
  unfold Z actInf; push_cast; ring

/-! ### The monodromy of a massless state of charge `(n_m, n_e)` -/

/-- `M(n_m, n_e) = [[1 + 2 n_e n_m, 2 n_e²], [-2 n_m², 1 - 2 n_m n_e]]` on the periods. -/
def actQ (nm ne : ℤ) (aD a : ℂ) : ℂ × ℂ :=
  ((1 + 2 * ne * nm : ℤ) * aD + (2 * ne ^ 2 : ℤ) * a,
   (-2 * nm ^ 2 : ℤ) * aD + (1 - 2 * nm * ne : ℤ) * a)

theorem actQ_det (nm ne : ℤ) :
    (1 + 2 * ne * nm) * (1 - 2 * nm * ne) - (2 * ne ^ 2) * (-2 * nm ^ 2) = 1 := by ring

/-- The state whose charge sets the monodromy keeps its own `Z`, with complex periods. -/
theorem Z_actQ_self (nm ne : ℤ) (aD a : ℂ) :
    Z nm ne (actQ nm ne aD a).1 (actQ nm ne aD a).2 = Z nm ne aD a := by
  unfold Z actQ; push_cast; ring

/-- So a state that is massless stays massless after going around its own singularity. -/
theorem massless_stays (nm ne : ℤ) (aD a : ℂ) (h : Z nm ne aD a = 0) :
    Z nm ne (actQ nm ne aD a).1 (actQ nm ne aD a).2 = 0 := by
  rw [Z_actQ_self, h]

/-- `M(1, 0) = M_1` and `M(1, -1) = M_{-1}` on the periods. -/
theorem actQ_monopole (aD a : ℂ) : actQ 1 0 aD a = act1 aD a := by
  unfold actQ act1; ext <;> simp

theorem actQ_dyon (aD a : ℂ) : actQ 1 (-1) aD a = actNeg1 aD a := by
  unfold actQ actNeg1; ext <;> simp

/-- Massless points: `a_D = 0` makes the monopole massless, `a_D = a` the dyon (Sections 5.3, 5.5). -/
theorem monopole_massless (a : ℂ) : mass 1 0 0 a = 0 := by simp [mass, Z]
theorem dyon_massless (a : ℂ) : mass 1 (-1) a a = 0 := by simp [mass, Z]

/-- `Z` is additive in the charges, so `|Z|` obeys the triangle inequality. -/
theorem mass_add_le (nm₁ ne₁ nm₂ ne₂ : ℤ) (aD a : ℂ) :
    mass (nm₁ + nm₂) (ne₁ + ne₂) aD a ≤ mass nm₁ ne₁ aD a + mass nm₂ ne₂ aD a := by
  unfold mass
  have hZ : Z (nm₁ + nm₂) (ne₁ + ne₂) aD a = Z nm₁ ne₁ aD a + Z nm₂ ne₂ aD a := by
    unfold Z; push_cast; ring
  rw [hZ, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg 2)

end SeibergWitten.CentralCharge
