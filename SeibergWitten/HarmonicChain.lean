import Lean

/-
  Algebraic slice of Seiberg–Witten, hep-th/9407087, §§5–6:
  charge-lattice monodromies, the pairing/trace identity, continued-fraction
  neighbor chains, and the algebraic coefficient identities from §6.

  Self-contained (core library only; no Mathlib). The source of the printed
  monodromy and period-coefficient statements is Seiberg and Witten as they
  wrote them. The chain experiments test lattice lifts, including a literal
  twin-prime charge lift that never hits trace -2.

  Lean does not prove analytic transport of the elliptic-curve periods or
  physical confinement. The effective_vacuum theorem is a conditional F-term
  implication.
-/

namespace SeibergWitten

structure Mat where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq, Repr

def mul (A B : Mat) : Mat :=
  ⟨A.a*B.a+A.b*B.c, A.a*B.b+A.b*B.d,
   A.c*B.a+A.d*B.c, A.c*B.b+A.d*B.d⟩

def adj (A : Mat) : Mat := ⟨A.d,-A.b,-A.c,A.a⟩
def tr (A : Mat) : Int := A.a + A.d
def det (A : Mat) : Int := A.a*A.d - A.b*A.c

structure Charge where
  m : Int
  e : Int
  deriving DecidableEq, Repr

def pairing (q r : Charge) : Int := q.m*r.e - q.e*r.m

def row (q : Charge) (A : Mat) : Charge :=
  ⟨q.m*A.a+q.e*A.c, q.m*A.b+q.e*A.d⟩

/-- Signed rank-one transvection with the paper's width-two normalization. -/
def twist (k : Int) (q : Charge) : Mat :=
  ⟨1+2*k*q.e*q.m, 2*k*q.e*q.e, -2*k*q.m*q.m, 1-2*k*q.m*q.e⟩

def mono (q : Charge) : Mat := twist 1 q

theorem twist_det (k : Int) (q : Charge) : det (twist k q) = 1 := by
  cases q
  simp only [det, twist]
  grind

theorem twist_fixes_charge (k : Int) (q : Charge) : row q (twist k q) = q := by
  cases q
  simp only [row, twist, Charge.mk.injEq]
  grind

theorem twist_add (k l : Int) (q : Charge) :
    mul (twist k q) (twist l q) = twist (k+l) q := by
  cases q
  simp only [mul, twist, Mat.mk.injEq]
  grind

theorem det_mul (A B : Mat) : det (mul A B) = det A * det B := by
  cases A
  cases B
  simp only [det, mul]
  grind

theorem pairing_covariant (q r : Charge) (A : Mat) :
    pairing (row q A) (row r A) = det A * pairing q r := by
  cases A
  cases q
  cases r
  simp only [pairing, row, det]
  grind

/-- Charge transforms contragrediently when periods transform by A.
    This proves equality of the central-charge pairing for all integer periods.
    The proof is a polynomial identity; no analytic input enters. -/
def column (A : Mat) (p : Int × Int) : Int × Int :=
  (A.a*p.1+A.b*p.2, A.c*p.1+A.d*p.2)

def central (q : Charge) (p : Int × Int) : Int := q.m*p.1 + q.e*p.2

theorem central_covariant (q : Charge) (A : Mat) (p : Int × Int) :
    central (row q (adj A)) (column A p) = det A * central q p := by
  cases A
  cases q
  cases p
  simp only [central, row, adj, column, det]
  grind

theorem twist_pair_trace (k l : Int) (q r : Charge) :
    tr (mul (twist k q) (twist l r)) = 2 - 4*k*l*(pairing q r)^2 := by
  cases q
  cases r
  simp only [tr, mul, twist, pairing]
  grind

theorem opposite_order_pair (q r : Charge) :
    tr (mul (mono q) (mono r)) = tr (mul (mono r) (mono q)) := by
  simp only [mono, twist_pair_trace, pairing]
  grind

theorem trace_minus_two_iff_neighbors (q r : Charge) :
    tr (mul (mono q) (mono r)) = -2 ↔ pairing q r = 1 ∨ pairing q r = -1 := by
  rw [mono, mono, twist_pair_trace]
  generalize pairing q r = z
  constructor
  · intro h
    have hz : (z-1)*(z+1) = 0 := by grind
    rcases Int.mul_eq_zero.mp hz with h1 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · intro h
    rcases h with h | h <;> simp [h]

def monopole : Charge := ⟨1,0⟩
def dyon : Charge := ⟨1,-1⟩
def mPlus : Mat := ⟨1,0,-2,1⟩
def mMinus : Mat := ⟨-1,2,-2,3⟩
def mInfinity : Mat := ⟨-1,2,0,-1⟩
def S : Mat := ⟨0,-1,1,0⟩
def T : Mat := ⟨1,1,0,1⟩
def translate (n : Int) : Mat := ⟨1,n,0,1⟩

/-- Eqs. (5.12), (5.13) and (6.1), in the paper's loop order. -/
theorem paper_matrices :
    mono monopole = mPlus ∧ mono dyon = mMinus ∧
    mul mPlus mMinus = mInfinity ∧ mul mMinus mPlus ≠ mInfinity := by decide

theorem cusp_frames :
    mul (adj S) (mul mPlus S) = translate 2 ∧
    mul (adj (mul T S)) (mul mMinus (mul T S)) = translate 2 ∧
    mInfinity = ⟨-1,2,0,-1⟩ := by decide

theorem cusp_translate_add (n j : Int) :
    mul (translate (2*n)) (translate (2*j)) = translate (2*(n+j)) := by
  simp only [mul, translate, Mat.mk.injEq]
  grind

/-- Subtracting twice the magnetic component gives the charge shift in §5.5,
    with the overall sign from the integral lift kept explicitly. -/
theorem infinity_charge_shift (q : Charge) :
    row q mInfinity = ⟨-q.m, -(q.e-2*q.m)⟩ := by
  cases q
  simp only [mInfinity, row, Charge.mk.injEq]
  grind

def straight (n : Int) : Charge := ⟨1,-n⟩

theorem straight_neighbor (n : Int) :
    tr (mul (mono (straight n)) (mono (straight (n+1)))) = -2 := by
  simp only [mono, twist_pair_trace, pairing, straight]
  grind

theorem straight_gap_trace (n j : Int) :
    tr (mul (mono (straight n)) (mono (straight (n+j)))) = 2-4*j^2 := by
  simp only [mono, twist_pair_trace, pairing, straight]
  grind

/-- A continued-fraction step replaces (q,r) by (r,q+k*r). -/
def nextCharge (q r : Charge) (k : Int) : Charge := ⟨q.m+k*r.m,q.e+k*r.e⟩

theorem continued_fraction_step (q r : Charge) (k : Int) :
    pairing r (nextCharge q r k) = -pairing q r := by
  cases q
  cases r
  simp only [pairing, nextCharge]
  grind

def chainStep (p : Charge × Charge) (k : Int) : Charge × Charge :=
  (p.2, nextCharge p.1 p.2 k)

theorem chain_pairing_sq (q r : Charge) (steps : List Int) :
    let p := steps.foldl chainStep (q,r)
    (pairing p.1 p.2)^2 = (pairing q r)^2 := by
  induction steps generalizing q r with
  | nil => rfl
  | cons k rest ih =>
    simp only [List.foldl_cons, chainStep]
    rw [ih, continued_fraction_step]
    grind

theorem chain_pair_trace (q r : Charge) (steps : List Int) :
    let p := steps.foldl chainStep (q,r)
    tr (mul (mono p.1) (mono p.2)) = tr (mul (mono q) (mono r)) := by
  dsimp only
  simp only [mono, twist_pair_trace]
  have h := chain_pairing_sq q r steps
  dsimp only at h
  rw [h]

/-- A twist adds a multiple of its vanishing charge to any transported charge. -/
theorem twist_charge_action (q r : Charge) (k : Int) :
    row q (twist k r) =
      ⟨q.m+2*k*(pairing q r)*r.m,q.e+2*k*(pairing q r)*r.e⟩ := by
  cases q
  cases r
  simp only [row, twist, pairing, Charge.mk.injEq]
  grind

theorem twist_conjugation (q : Charge) (A : Mat) (k : Int) (h : det A = 1) :
    twist k (row q A) = mul (adj A) (mul (twist k q) A) := by
  cases q
  cases A
  simp only [row, twist, adj, mul, Mat.mk.injEq, det] at *
  grind

/-- This deliberately tests the literal lift of a twin pair into the charge lattice. -/
theorem twin_pair_literal_lift (a b : Int) :
    pairing ⟨a,a+2⟩ ⟨b,b+2⟩ = 2*(a-b) := by
  simp only [pairing]
  grind

theorem twin_pair_literal_lift_fails (a b : Int) :
    tr (mul (mono ⟨a,a+2⟩) (mono ⟨b,b+2⟩)) ≠ -2 := by
  intro h
  have hpair := (trace_minus_two_iff_neighbors ⟨a,a+2⟩ ⟨b,b+2⟩).mp h
  rw [twin_pair_literal_lift] at hpair
  omega

/-- Adjacent trace alignment cannot imply alignment of all ordered products. -/
theorem three_step_negative_control :
    tr (mul (mul (mono (straight 0)) (mono (straight 1))) (mono (straight 2))) = -6 := by
  decide

def curve (u x : Int) : Int := (x-1)*(x+1)*(x-u)
def disc (u : Int) : Int := 4*(u-1)^2*(u+1)^2

theorem discriminant_factor (u : Int) : disc u = 4*(u^2-1)^2 := by
  simp only [disc]
  grind

theorem cubic_discriminant (u : Int) :
    let b := -u
    let c : Int := -1
    let d := u
    b^2*c^2-4*c^3-4*b^3*d-27*d^2+18*b*c*d = disc u := by
  simp only [disc]
  grind

theorem curve_expansion (u x : Int) : curve u x = x^3-u*x^2-x+u := by
  simp only [curve]
  grind

/-- Numerator identity in the exact-x-differential certificate for the period ODE.
    Multiply 2f - (x-u)∂ₓf by -1 to match the derivative of y/(x-u). -/
theorem picard_fuchs_numerator (u x : Int) :
    (x-u)*(3*x^2-2*u*x-1)-2*curve u x =
      (x-u)*((x-u)^2-(u^2-1)) := by
  simp only [curve]
  grind

/-- Match the coefficient for z^(n+1) after inserting z^(n+1) and z^(n+2)
    into (z²+2z) d²/dz² + 1/4 and clearing 4. -/
theorem local_recurrence_coefficients (n b c : Int) :
    4*((n+1)*n*b+2*(n+2)*(n+1)*c)+b =
      (2*n+1)^2*b+8*(n+2)*(n+1)*c := by grind

/-- Coefficient for u^(1/2-2(n+1)) after clearing 4 in
    (u²-1) d²/du² + 1/4. -/
theorem infinity_recurrence_coefficients (n b c : Int) :
    (((1-4*(n+1))*(-1-4*(n+1))+1)*c) -
       (1-4*n)*(-1-4*n)*b =
      16*(n+1)^2*c-(16*n^2-1)*b := by grind

/-- Imaginary part of Z(q) times the conjugate of Z(r), in real coordinates.
    This is an alignment criterion; stability still depends on the spectrum. -/
theorem central_phase_pairing {R : Type} [Lean.Grind.CommRing R]
    (qm qe rm re dR dI aR aI : R) :
    (qm*dI+qe*aI)*(rm*dR+re*aR)-(qm*dR+qe*aR)*(rm*dI+re*aI) =
      (qm*re-qe*rm)*(dI*aR-dR*aI) := by
  grind

/-- Given the logarithm's branch jump, recover the coefficient and sign of §5.4. -/
theorem local_log_jump {R : Type} [Lean.Grind.CommRing R]
    (i pi invPi aD regular logValue : R)
    (hi : i*i = -1) (hp : invPi*pi = 1) :
    regular+i*invPi*aD*(logValue+2*pi*i) =
      regular+i*invPi*aD*logValue-2*aD := by
  grind

/-- Given the same jump and the square-root sign at infinity, recover Eq. (5.3). -/
theorem infinity_log_jump {R : Type} [Lean.Grind.CommRing R]
    (i pi invPi a regular logValue : R)
    (hi : i*i = -1) (hp : invPi*pi = 1) :
    -regular+i*invPi*(-a)*(logValue+2*pi*i) =
      -(regular+i*invPi*a*logValue)+2*a := by
  grind

/-- Algebra of §5.6 eq. (5.20), with the coefficient of M M̃ kept symbolic.
    The no-zero-products premise holds in the intended complex coefficient field. -/
theorem effective_vacuum
    {R : Type} [Lean.Grind.CommRing R]
    (noZeroProducts : ∀ x y : R, x*y = 0 → x = 0 ∨ y = 0)
    (aD M Mtilde coupling perturbation slope : R)
    (hc : coupling*(M*Mtilde) + perturbation*slope = 0)
    (hm : perturbation*slope ≠ 0) (ha : aD*M = 0) :
    aD = 0 ∧ M ≠ 0 ∧ Mtilde ≠ 0 := by
  have hM : M ≠ 0 := by
    intro h
    subst M
    apply hm
    grind
  have hMt : Mtilde ≠ 0 := by
    intro h
    subst Mtilde
    apply hm
    grind
  exact ⟨(noZeroProducts aD M ha).resolve_right hM, hM, hMt⟩

end SeibergWitten

