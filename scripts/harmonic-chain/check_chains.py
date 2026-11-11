"""Exact integer/rational checks and independent real-slice period quadrature."""

from fractions import Fraction
from math import cos, gcd, pi, sin, sqrt
from functools import reduce


def pair(q, r):
    return q[0] * r[1] - q[1] * r[0]


def twist(q):
    m, e = q
    return 1 + 2*m*e, 2*e*e, -2*m*m, 1 - 2*m*e


def mul(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h


def trace(A):
    return A[0] + A[3]


def chain(steps):
    out = [(1, 0), (1, -1)]
    for k in steps:
        q, r = out[-2:]
        out.append((q[0]+k*r[0], q[1]+k*r[1]))
    return out


def chain_test(name, charges, expected_trace):
    assert all(gcd(m, e) == 1 for m, e in charges)
    neighbors = list(zip(charges, charges[1:]))
    pairings = [pair(q, r) for q, r in neighbors]
    traces = [trace(mul(twist(q), twist(r))) for q, r in neighbors]
    assert traces == [2-4*d*d for d in pairings]
    assert all(expected_trace(t) for t in traces)
    ordered = reduce(mul, map(twist, charges))
    print(f"{name}: {charges}")
    print(f"  adjacent pairings {pairings}, traces {traces}, full trace {trace(ordered)}")


def coefficients(ratio, count=96):
    c = [Fraction(1)]
    for n in range(count-1):
        c.append(c[-1]*ratio(n))
    return c


def evaluate(c, z):
    acc = 0.0
    for coeff in reversed(c):
        acc = float(coeff)+z*acc
    return acc


def simpson(f, a, b, n=4096):
    step = (b-a)/n
    return step/3*(f(a)+f(b)+sum((4 if i % 2 else 2)*f(a+i*step) for i in range(1,n)))


def main():
    P, D = twist((1, 0)), twist((1, -1))
    assert mul(P, D) == (-1, 2, 0, -1)
    assert mul(D, P) != mul(P, D)
    assert trace(mul(mul(P,D),twist((1,-2)))) == -6
    chain_test("Straight", [(1, -n) for n in range(7)], lambda t: t == -2)
    chain_test("Fibonacci", chain([1]*5), lambda t: t == -2)
    chain_test("Pell", chain([2]*5), lambda t: t == -2)
    chain_test("Mixed", chain([1, 3, 2, 5, 1]), lambda t: t == -2)
    chain_test("Skipped charges", [(1, -2*n) for n in range(7)], lambda t: t == -14)
    chain_test("Literal twin-prime lift", [(p,p+2) for p in (5, 11, 17, 29, 41)], lambda t: t < -2)

    # In a width-two local frame s goes to s+2. In the reciprocal coordinate
    # the iterates are harmonic. This is an algebraic sample, not the modulus u.
    s0 = Fraction(3)
    for n in range(10):
        w = 1/(s0+2*n)
        assert w/(1+2*w) == 1/(s0+2*(n+1))

    far = coefficients(lambda n: Fraction(16*n*n-1,16*(n+1)**2))
    near = coefficients(lambda n: Fraction(-(2*n+1)**2,8*(n+1)*(n+2)))
    assert far[:3] == [1,Fraction(-1,16),Fraction(-15,1024)]
    assert near[:3] == [1,Fraction(-1,16),Fraction(3,256)]
    for u in (1.25,1.5,2.0,2.5):
        z = u-1
        a = sqrt(2*u)*evaluate(far,1/u**2)
        imag_aD = z/2*evaluate(near,z)
        a_int = sqrt(2)/pi*simpson(lambda t: sqrt(u-cos(t)),0,pi)
        aD_int = sqrt(2)/pi*z*simpson(lambda t: 2*cos(t)**2/sqrt(2+z*sin(t)**2),0,pi/2)
        da, dD = abs(a-a_int), abs(imag_aD-aD_int)
        assert max(da,dD) < 1e-10
        print(f"u={u:.2f}: a={a:.12f}, a_D=i*{imag_aD:.12f}, quadrature errors {da:.2e}, {dD:.2e}")


if __name__ == "__main__":
    main()
