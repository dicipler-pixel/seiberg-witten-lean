import SeibergWitten.Monodromy

/-!
# Section 5: structure of the three monodromies

Seiberg and Witten, hep-th/9407087, Sections 5.1, 5.4 and 5.5. Additions to `Monodromy.lean`,
on the same `Mat2` and `Charge` (no Mathlib):

* the traces are `-2`, `2`, `2`;
* each monodromy is `±1` plus a nonzero matrix of square zero, which is the matrix form of the
  logarithm in `a ≈ a₀ + (i/π) a_D ln a_D` and in the one-loop formula;
* the charges fixed by `M₁` are exactly the multiples of the monopole `(1, 0)`, and the charges
  fixed by `M₋₁` are exactly the multiples of the dyon `(1, -1)`.
-/

namespace SeibergWitten.Monodromy

def Mat2.tr (A : Mat2) : Int := A.a11 + A.a22

def Mat2.add (A B : Mat2) : Mat2 :=
  { a11 := A.a11 + B.a11, a12 := A.a12 + B.a12, a21 := A.a21 + B.a21, a22 := A.a22 + B.a22 }

def one : Mat2 := { a11 := 1, a12 := 0, a21 := 0, a22 := 1 }
def zero : Mat2 := { a11 := 0, a12 := 0, a21 := 0, a22 := 0 }

theorem tr_M_inf : M_inf.tr = -2 := rfl
theorem tr_M1 : M1.tr = 2 := rfl
theorem tr_Mneg1 : Mneg1.tr = 2 := rfl

/-- `M₁ - 1`. -/
def N1 : Mat2 := { a11 := 0, a12 := 0, a21 := -2, a22 := 0 }
/-- `M₋₁ - 1`. -/
def Nneg1 : Mat2 := { a11 := -2, a12 := 2, a21 := -2, a22 := 2 }
/-- `M∞ + 1`. -/
def N_inf : Mat2 := { a11 := 0, a12 := 2, a21 := 0, a22 := 0 }

theorem M1_eq_one_add : M1 = Mat2.add one N1 := rfl
theorem N1_sq : N1 * N1 = zero := rfl
theorem N1_ne_zero : N1 ≠ zero := by decide

theorem Mneg1_eq_one_add : Mneg1 = Mat2.add one Nneg1 := rfl
theorem Nneg1_sq : Nneg1 * Nneg1 = zero := rfl
theorem Nneg1_ne_zero : Nneg1 ≠ zero := by decide

theorem M_inf_eq_P_add : M_inf = Mat2.add P N_inf := rfl
theorem N_inf_sq : N_inf * N_inf = zero := rfl
theorem N_inf_ne_zero : N_inf ≠ zero := by decide

/-- Section 5.5: the charges fixed by `M₁` are exactly those with `n_e = 0`. -/
theorem fixed_by_M1_iff (q : Charge) : q * M1 = q ↔ q.n_e = 0 := by
  cases q with
  | mk m e =>
    show Charge.mk (m * 1 + e * (-2)) (m * 0 + e * 1) = Charge.mk m e ↔ e = 0
    rw [Charge.mk.injEq]
    constructor
    · intro h; omega
    · intro h; subst h; constructor <;> omega

/-- Section 5.5: the charges fixed by `M₋₁` are exactly those with `n_m + n_e = 0`. -/
theorem fixed_by_Mneg1_iff (q : Charge) : q * Mneg1 = q ↔ q.n_m + q.n_e = 0 := by
  cases q with
  | mk m e =>
    show Charge.mk (m * (-1) + e * (-2)) (m * 2 + e * 3) = Charge.mk m e ↔ m + e = 0
    rw [Charge.mk.injEq]
    constructor
    · intro h; omega
    · intro h; constructor <;> omega

end SeibergWitten.Monodromy
