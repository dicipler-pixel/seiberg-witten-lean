/-
  Electric-Magnetic Duality, Monopole Condensation, And Confinement
  In N=2 Supersymmetric Yang-Mills Theory
  N. Seiberg and E. Witten, hep-th/9407087 (1994), §5.

  The monodromy matrices of the u-plane (their eqs. (5.3), (5.12)–(5.15) and (6.1))
  and the charge vectors of the particles that become massless at each puncture.

  This file is self-contained (no Mathlib) so it can be kernel-checked immediately.
-/

namespace SeibergWitten.Monodromy

structure Mat2 where
  a11 : Int
  a12 : Int
  a21 : Int
  a22 : Int
deriving DecidableEq, Repr

def Mat2.mul (A B : Mat2) : Mat2 :=
  { a11 := A.a11 * B.a11 + A.a12 * B.a21
    a12 := A.a11 * B.a12 + A.a12 * B.a22
    a21 := A.a21 * B.a11 + A.a22 * B.a21
    a22 := A.a21 * B.a12 + A.a22 * B.a22 }

instance : Mul Mat2 := ⟨Mat2.mul⟩

def Mat2.det (A : Mat2) : Int := A.a11 * A.a22 - A.a12 * A.a21

/-- Charge row vector (n_m, n_e). -/
structure Charge where
  n_m : Int
  n_e : Int
deriving DecidableEq, Repr

/-- Right action q ↦ q M, as in the paper: the massless particle producing M obeys q M = q. -/
def Charge.mulMat (q : Charge) (M : Mat2) : Charge :=
  { n_m := q.n_m * M.a11 + q.n_e * M.a21
    n_e := q.n_m * M.a12 + q.n_e * M.a22 }

instance : HMul Charge Mat2 Charge := ⟨Charge.mulMat⟩

/-- T = [[1, 1], [0, 1]], the elementary θ-shift. -/
def T : Mat2 := { a11 := 1, a12 := 1, a21 := 0, a22 := 1 }

/-- S = [[0, 1], [-1, 0]], electric-magnetic duality. -/
def S : Mat2 := { a11 := 0, a12 := 1, a21 := -1, a22 := 0 }

/-- P = −I ∈ SL(2, ℤ). -/
def P : Mat2 := { a11 := -1, a12 := 0, a21 := 0, a22 := -1 }

/-- Inverse of T. -/
def Tinv : Mat2 := { a11 := 1, a12 := -1, a21 := 0, a22 := 1 }

/-- Inverse of S. S⁻¹ = [[0, −1], [1, 0]]. -/
def Sinv : Mat2 := { a11 := 0, a12 := -1, a21 := 1, a22 := 0 }

/-- Monodromy at infinity: M_∞ = P T⁻² = [[−1, 2], [0, −1]]. -/
def M_inf : Mat2 := { a11 := -1, a12 := 2, a21 := 0, a22 := -1 }

/-- Monodromy at the massless-monopole puncture (paper: u = 1): M₁ = S T² S⁻¹ = [[1, 0], [−2, 1]]. -/
def M1 : Mat2 := { a11 := 1, a12 := 0, a21 := -2, a22 := 1 }

/-- Monodromy at the massless-dyon puncture (paper: u = −1): M₋₁ = [[−1, 2], [−2, 3]]. -/
def Mneg1 : Mat2 := { a11 := -1, a12 := 2, a21 := -2, a22 := 3 }

theorem det_T : T.det = 1 := rfl
theorem det_S : S.det = 1 := rfl
theorem det_P : P.det = 1 := rfl
theorem det_M_inf : M_inf.det = 1 := rfl
theorem det_M1 : M1.det = 1 := rfl
theorem det_Mneg1 : Mneg1.det = 1 := rfl

theorem T_mul_Tinv : T * Tinv = { a11 := 1, a12 := 0, a21 := 0, a22 := 1 } := rfl
theorem Tinv_mul_T : Tinv * T = { a11 := 1, a12 := 0, a21 := 0, a22 := 1 } := rfl
theorem S_mul_Sinv : S * Sinv = { a11 := 1, a12 := 0, a21 := 0, a22 := 1 } := rfl
theorem Sinv_mul_S : Sinv * S = { a11 := 1, a12 := 0, a21 := 0, a22 := 1 } := rfl

/-- T² = [[1, 2], [0, 1]]. -/
theorem T_sq : T * T = { a11 := 1, a12 := 2, a21 := 0, a22 := 1 } := rfl

/-- T⁻² = [[1, −2], [0, 1]]. -/
theorem Tinv_sq : Tinv * Tinv = { a11 := 1, a12 := -2, a21 := 0, a22 := 1 } := rfl

/-- M_∞ = P T⁻². -/
theorem M_inf_eq_P_Tinv_sq : P * (Tinv * Tinv) = M_inf := rfl

/-- M₁ = S T² S⁻¹. -/
theorem M1_eq_S_Tsq_Sinv : S * (T * T) * Sinv = M1 := rfl

/-- The monodromies compose: M₁ M₋₁ = M_∞. -/
theorem M1_mul_Mneg1_eq_M_inf : M1 * Mneg1 = M_inf := rfl

/-- Massless monopole of charges (n_m, n_e) = (1, 0) is fixed by M₁. -/
def q1 : Charge := { n_m := 1, n_e := 0 }

theorem q1_fixed_by_M1 : q1 * M1 = q1 := rfl

/-- Massless (1, −1) dyon is fixed by M₋₁. -/
def qneg1 : Charge := { n_m := 1, n_e := -1 }

theorem qneg1_fixed_by_Mneg1 : qneg1 * Mneg1 = qneg1 := rfl

/-- Conjugation matrix A = T M₁ used in the paper, with A M₁ A⁻¹ = M₋₁. -/
def A : Mat2 := { a11 := -1, a12 := 1, a21 := -2, a22 := 1 }

theorem A_eq_T_mul_M1 : T * M1 = A := rfl

/-- Inverse of A: det A = 1, so A⁻¹ = [[1, −1], [2, −1]]. -/
def Ainv : Mat2 := { a11 := 1, a12 := -1, a21 := 2, a22 := -1 }

theorem A_mul_Ainv : A * Ainv = { a11 := 1, a12 := 0, a21 := 0, a22 := 1 } := rfl
theorem Ainv_mul_A : Ainv * A = { a11 := 1, a12 := 0, a21 := 0, a22 := 1 } := rfl
theorem det_A : A.det = 1 := rfl

/-- M₋₁ = A M₁ A⁻¹. -/
theorem Mneg1_eq_A_conj_M1 : A * M1 * Ainv = Mneg1 := rfl

/-- A² = −I = P. -/
theorem A_sq_eq_P : A * A = P := rfl

/-- Inverse of T S. (T S)⁻¹ = [[0, −1], [1, −1]]. -/
def TSinv : Mat2 := { a11 := 0, a12 := -1, a21 := 1, a22 := -1 }

theorem TS_mul_TSinv : (T * S) * TSinv = { a11 := 1, a12 := 0, a21 := 0, a22 := 1 } := rfl
theorem TSinv_mul_TS : TSinv * (T * S) = { a11 := 1, a12 := 0, a21 := 0, a22 := 1 } := rfl

/-- Paper (5.13): M₋₁ = (T S) T² (T S)⁻¹. -/
theorem Mneg1_eq_TS_Tsq_TSinv : (T * S) * (T * T) * TSinv = Mneg1 := rfl

end SeibergWitten.Monodromy
