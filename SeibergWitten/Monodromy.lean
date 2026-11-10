import Mathlib

/-!
# Section 5: The monodromies

Seiberg and Witten, hep-th/9407087, Sections 5.1, 5.4 and 5.5.

The pair `(a_D, a)` is not single valued on the `u`-plane. Round the three singular points it is
multiplied by

* `M∞ = P T⁻² = [-1, 2 ; 0, -1]` (Section 5.1),
* `M₁ = S T² S⁻¹ = [1, 0 ; -2, 1]` (Section 5.4),
* `M₋₁ = (TS) T² (TS)⁻¹ = [-1, 2 ; -2, 3]` (Section 5.5),

with `M₁ M₋₁ = M∞`. Inverses are avoided in the statements: `X = Y Z⁻¹` is written `X * Z = Y`.
-/

namespace SeibergWitten

open Matrix

/-- Two by two matrices of integers. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℤ

/-- `S`, which exchanges `a` and `a_D` (Section 3.2). -/
def S : Mat2 := !![0, 1; -1, 0]
/-- `T`, the shift `a_D → a_D + a` (Section 3.2). -/
def T : Mat2 := !![1, 1; 0, 1]
/-- `P`, the element `-1` (Section 5.1). -/
def P : Mat2 := !![-1, 0; 0, -1]
/-- The monodromy at infinity (Section 5.1). -/
def Minf : Mat2 := !![-1, 2; 0, -1]
/-- The monodromy round `u = 1`, where the monopole is massless (Section 5.4). -/
def M1 : Mat2 := !![1, 0; -2, 1]
/-- The monodromy round `u = -1` (Section 5.5). -/
def Mneg1 : Mat2 := !![-1, 2; -2, 3]
/-- The matrix `A = T M₁` that conjugates `M₁` to `M₋₁` (Section 5.5). -/
def A : Mat2 := !![-1, 1; -2, 1]
/-- The inverse of `M∞`. -/
def MinfInv : Mat2 := !![-1, -2; 0, -1]
/-- `M₁ - 1`. -/
def N1 : Mat2 := !![0, 0; -2, 0]
/-- `M₋₁ - 1`. -/
def Nneg1 : Mat2 := !![-2, 2; -2, 2]
/-- `M∞ + 1`. -/
def Ninf : Mat2 := !![0, 2; 0, 0]

/-- Closes an identity between explicit two by two integer matrices. -/
macro "mat2_id" : tactic =>
  `(tactic| first
    | (simp [S, T, P, Minf, M1, Mneg1, A, MinfInv, N1, Nneg1, Ninf, Matrix.mul_fin_two,
        Matrix.one_fin_two]; done)
    | (ext i j; fin_cases i <;> fin_cases j <;>
        simp [S, T, P, Minf, M1, Mneg1, A, MinfInv, N1, Nneg1, Ninf, Matrix.mul_apply,
          Fin.sum_univ_two])
    | decide)

/-- Section 5.5: `M₁ M₋₁ = M∞`. -/
theorem M1_mul_Mneg1 : M1 * Mneg1 = Minf := by mat2_id

/-- Section 5.1: `M∞ = P T⁻²`, written `M∞ T² = P`. -/
theorem Minf_mul_T_sq : Minf * (T * T) = P := by mat2_id

/-- Section 5.4: `M₁ = S T² S⁻¹`, written `M₁ S = S T²`. -/
theorem M1_mul_S : M1 * S = S * (T * T) := by mat2_id

/-- Section 5.5: `M₋₁ = (TS) T² (TS)⁻¹`, written `M₋₁ (TS) = (TS) T²`. -/
theorem Mneg1_mul_TS : Mneg1 * (T * S) = (T * S) * (T * T) := by mat2_id

/-- Section 5.5: `A = T M₁`. -/
theorem A_eq : A = T * M1 := by mat2_id

/-- Section 5.5: `M₋₁ = A M₁ A⁻¹`, written `M₋₁ A = A M₁`. -/
theorem Mneg1_mul_A : Mneg1 * A = A * M1 := by mat2_id

/-- Section 5.5: `A² = -1`. -/
theorem A_mul_A : A * A = P := by mat2_id

/-- `P` is minus the identity. -/
theorem P_eq : P = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [P]

/-- `MinfInv` is the inverse of `M∞`. -/
theorem Minf_mul_MinfInv : Minf * MinfInv = 1 := by mat2_id

/-- `MinfInv` is the inverse of `M∞`, on the other side. -/
theorem MinfInv_mul_Minf : MinfInv * Minf = 1 := by mat2_id

/-- The three monodromies have determinant one. -/
theorem det_Minf : Minf.det = 1 := by simp [Minf, Matrix.det_fin_two_of]
theorem det_M1 : M1.det = 1 := by simp [M1, Matrix.det_fin_two_of]
theorem det_Mneg1 : Mneg1.det = 1 := by simp [Mneg1, Matrix.det_fin_two_of]

/-- The traces: `-2` at infinity and `2` at the two finite singular points. -/
theorem trace_Minf : Minf.trace = -2 := by simp [Minf, Matrix.trace_fin_two_of]
theorem trace_M1 : M1.trace = 2 := by simp [M1, Matrix.trace_fin_two_of]
theorem trace_Mneg1 : Mneg1.trace = 2 := by simp [Mneg1, Matrix.trace_fin_two_of]

/-- `M₁ = 1 + N₁` with `N₁² = 0`: the monodromy of the logarithm `a ≈ a₀ + (i/π) a_D ln a_D`. -/
theorem M1_eq : M1 = 1 + N1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [M1, N1]
theorem N1_mul_N1 : N1 * N1 = 0 := by mat2_id

/-- `M₋₁ = 1 + N₋₁` with `N₋₁² = 0`. -/
theorem Mneg1_eq : Mneg1 = 1 + Nneg1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Mneg1, Nneg1]
theorem Nneg1_mul_Nneg1 : Nneg1 * Nneg1 = 0 := by mat2_id

/-- `M∞ = -1 + N∞` with `N∞² = 0`. -/
theorem Minf_eq : Minf = -1 + Ninf := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Minf, Ninf]
theorem Ninf_mul_Ninf : Ninf * Ninf = 0 := by mat2_id

/-- The row of charges `(n_m, n_e)` multiplied on the right by a matrix (Section 4). -/
def rowAct (nm ne : ℤ) (M : Mat2) : ℤ × ℤ :=
  (nm * M 0 0 + ne * M 1 0, nm * M 0 1 + ne * M 1 1)

theorem rowAct_M1 (nm ne : ℤ) : rowAct nm ne M1 = (nm * 1 + ne * (-2), nm * 0 + ne * 1) := by
  first | rfl | simp [rowAct, M1]

theorem rowAct_Mneg1 (nm ne : ℤ) :
    rowAct nm ne Mneg1 = (nm * (-1) + ne * (-2), nm * 2 + ne * 3) := by
  first | rfl | simp [rowAct, Mneg1]

theorem rowAct_MinfInv (nm ne : ℤ) :
    rowAct nm ne MinfInv = (nm * (-1) + ne * 0, nm * (-2) + ne * (-1)) := by
  first | rfl | simp [rowAct, MinfInv]

/-- Section 5.5: the charges left unchanged by `M₁` are the multiples of the monopole `(1, 0)`. -/
theorem rowAct_M1_fixed_iff (nm ne : ℤ) : rowAct nm ne M1 = (nm, ne) ↔ ne = 0 := by
  rw [rowAct_M1, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, -⟩; omega
  · intro h; subst h; constructor <;> ring

/-- Section 5.5: the charges left unchanged by `M₋₁` are the multiples of the dyon `(1, -1)`. -/
theorem rowAct_Mneg1_fixed_iff (nm ne : ℤ) : rowAct nm ne Mneg1 = (nm, ne) ↔ nm + ne = 0 := by
  rw [rowAct_Mneg1, Prod.mk.injEq]
  constructor
  · rintro ⟨h1, -⟩; omega
  · intro h; constructor <;> omega

/-- Section 5.1: at infinity the charges go to `(-n_m, -n_e - 2 n_m)`. -/
theorem rowAct_MinfInv_eq (nm ne : ℤ) : rowAct nm ne MinfInv = (-nm, -ne - 2 * nm) := by
  rw [rowAct_MinfInv, Prod.mk.injEq]
  constructor <;> ring

end SeibergWitten
