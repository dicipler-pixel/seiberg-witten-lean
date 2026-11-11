import Std

/-!
# Period series near `u = ∞` and `u = 1`

Seiberg and Witten, hep-th/9407087, §6, eqs. (6.24)–(6.27).

The paper gives the leading behaviour
* (6.24) `a ≈ √(2u)` near `u = ∞`;
* (6.27) `a_D ≈ (i/2)(1 - 1/u) ≈ i(u - 1)/2` near `u = 1`.

Both periods satisfy the Picard–Fuchs equation `(u² - 1) Π'' + Π/4 = 0`
(the numerator identity is `picard_fuchs_numerator` in `HarmonicChain.lean`).
Here we define the two power-series coefficient sequences that solve that
equation, with the paper's leading normalizations, and prove in exact
rational arithmetic that each coefficient balances the equation:

* near infinity, `a(u) = √(2u) · Σ cInf n · u^(-2n)`, `cInf 0 = 1`;
* near the monopole point, `a_D(u) = (i/2) · Σ bOne n · (u - 1)^(n+1)`, `bOne 0 = 1`.

What is proved is coefficient algebra: the formal series solve the equation term by
term and start with the paper's leading terms. Convergence, the identification
of these series with the actual period integrals (6.22)–(6.23), and the
logarithmic terms (6.26), (6.30) are not proved here.
-/

namespace SeibergWitten.PeriodSeries

/-- Coefficients of `a(u) / √(2u)` in powers of `u⁻²` (large `u`). -/
def cInf : Nat → Rat
  | 0 => 1
  | n + 1 => cInf n * (16 * (n : Rat) * n - 1) / (16 * ((n : Rat) + 1) * ((n : Rat) + 1))

/-- Coefficients of `a_D(u) / (i/2)` in powers of `(u - 1)`, starting at `(u - 1)¹`. -/
def bOne : Nat → Rat
  | 0 => 1
  | n + 1 => -(bOne n * ((2 * (n : Rat) + 1) * (2 * (n : Rat) + 1)))
              / (8 * ((n : Rat) + 1) * ((n : Rat) + 2))

/-- Eq. (6.24): the leading term of `a` at large `u` is exactly `√(2u)`. -/
theorem cInf_leading : cInf 0 = 1 := rfl

/-- Eq. (6.27): the leading term of `a_D` near `u = 1` is exactly `i(u - 1)/2`. -/
theorem bOne_leading : bOne 0 = 1 := rfl

theorem cInf_one : cInf 1 = -1/16 := by simp only [cInf]; grind
theorem cInf_two : cInf 2 = -15/1024 := by simp only [cInf]; grind
theorem bOne_one : bOne 1 = -1/16 := by simp only [bOne]; grind
theorem bOne_two : bOne 2 = 3/256 := by simp only [bOne]; grind

/-- Exponent of the `n`-th term near infinity: `u^(1/2 - 2n)`. -/
def alpha (n : Nat) : Rat := 1/2 - 2 * (n : Rat)

/-- Picard–Fuchs balance at `u = ∞`, term by term.
    With `Π = Σ cₙ u^(αₙ)`, the coefficient of `u^(α_{n+1})` in
    `(u² - 1) Π'' + Π/4` is `(α_{n+1}(α_{n+1} - 1) + 1/4) c_{n+1} - αₙ(αₙ - 1) cₙ`. -/
theorem cInf_picard_fuchs (n : Nat) :
    (alpha (n+1) * (alpha (n+1) - 1) + 1/4) * cInf (n+1)
      - alpha n * (alpha n - 1) * cInf n = 0 := by
  have h1 : ((n : Rat) + 1) ≠ 0 := by
    have : (0 : Rat) < (n : Rat) + 1 := by grind
    grind
  have hd : (16 * ((n : Rat) + 1) * ((n : Rat) + 1)) ≠ 0 := by grind
  simp only [cInf, alpha]
  have key : cInf n * (16 * (n : Rat) * n - 1) / (16 * ((n : Rat) + 1) * ((n : Rat) + 1))
      * (16 * ((n : Rat) + 1) * ((n : Rat) + 1)) = cInf n * (16 * (n : Rat) * n - 1) :=
    Rat.div_mul_cancel hd
  grind

/-- The lowest exponent `u^(1/2)` is allowed: its indicial factor vanishes. -/
theorem cInf_indicial : alpha 0 * (alpha 0 - 1) + 1/4 = 0 := by
  simp only [alpha]; grind

/-- Picard–Fuchs balance near `u = 1`, term by term, in `z = u - 1`
    (so `u² - 1 = z² + 2z`). With `Π = Σ bₙ z^(n+1)`, the coefficient of
    `z^(n+1)` in `(z² + 2z) Π'' + Π/4` is
    `(n+1) n bₙ + 2 (n+2)(n+1) b_{n+1} + bₙ/4`. -/
theorem bOne_picard_fuchs (n : Nat) :
    ((n : Rat) + 1) * n * bOne n + 2 * ((n : Rat) + 2) * ((n : Rat) + 1) * bOne (n+1)
      + bOne n / 4 = 0 := by
  have h1 : ((n : Rat) + 1) ≠ 0 := by
    have : (0 : Rat) < (n : Rat) + 1 := by grind
    grind
  have h2 : ((n : Rat) + 2) ≠ 0 := by
    have : (0 : Rat) < (n : Rat) + 2 := by grind
    grind
  have hd : (8 * ((n : Rat) + 1) * ((n : Rat) + 2)) ≠ 0 := by grind
  simp only [bOne]
  have key : -(bOne n * ((2 * (n : Rat) + 1) * (2 * (n : Rat) + 1)))
      / (8 * ((n : Rat) + 1) * ((n : Rat) + 2)) * (8 * ((n : Rat) + 1) * ((n : Rat) + 2))
      = -(bOne n * ((2 * (n : Rat) + 1) * (2 * (n : Rat) + 1))) :=
    Rat.div_mul_cancel hd
  grind

/-- The lowest power `z⁰` carries no condition, so `a_D` may start at `z¹`
    as in (6.27): its coefficient `2 · 1 · 0 · b₀` is zero. -/
theorem bOne_lowest : 2 * (1 : Rat) * 0 * bOne 0 = 0 := by grind

/-- Eq. (6.27), the step `(i/2)(1 - 1/u) ≈ i(u - 1)/2`: the exact difference
    is second order in `u - 1`. -/
theorem near_one_leading (u : Rat) (hu : u ≠ 0) :
    (1 - 1/u) - (u - 1) = -((u - 1) * (u - 1)) / u := by
  have k1 : 1 / u * u = 1 := Rat.div_mul_cancel hu
  have k2 : -((u - 1) * (u - 1)) / u * u = -((u - 1) * (u - 1)) := Rat.div_mul_cancel hu
  grind

end SeibergWitten.PeriodSeries
