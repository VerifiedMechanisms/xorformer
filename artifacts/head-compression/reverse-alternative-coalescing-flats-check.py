"""Exact identities behind reverse-alternative-coalescing-flats.tex."""

import sympy as s

t, W, eps, delta, eta, V = s.symbols("t W eps delta eta V")

# Binary decomposition is exact separately at each allowed profile value.
for value in (-1, 1):
    lhs = 1 / (1 - eps * W - delta - eta * value)
    rhs = (1 + value) / (2 * (1 - eps * W - delta - eta))
    rhs += (1 - value) / (2 * (1 - eps * W - delta + eta))
    assert s.cancel(lhs - rhs) == 0

# The finite numerator-space operator has the claimed eigenvectors.
lambdas = [t, 2 * t, 3 * t, s.Rational(5, 3) * t + t**2]
D = s.prod(1 - a * W for a in lambdas)
for a in lambdas:
    numerator = s.cancel(D / (1 - a * W))
    shifted = s.cancel((numerator - numerator.subs(W, 0) * D) / W)
    assert s.cancel(shifted - a * numerator) == 0

profiles = [s.Matrix(v) for v in ((1, 0), (0, 1), (1, 1), (1, -1))]
f = [v / (1 - a * W) for v, a in zip(profiles, lambdas)]
g3 = f[2] - f[0] - f[1]
g4 = f[3] - f[0] + f[1]
basis = [f[0], f[1], g3 / t, (3 * g4 - g3) / t**2]
u = s.Matrix([2, 1])
expected = [profiles[0], profiles[1], u * W,
            3 * s.Matrix([1, -1]) * W - s.Rational(4, 3) * u * W**2]
for vector, target in zip(basis, expected):
    limit = vector.applyfunc(lambda z: s.limit(z, t, 0))
    assert limit == target

def coeffs(vector):
    return s.Matrix([s.expand(vector[j]).coeff(W, k)
                     for k in range(3) for j in range(2)])

matrix = s.Matrix.hstack(*(coeffs(v) for v in expected))
assert matrix.rank() == 4
for vector in expected:
    shift = vector.applyfunc(lambda z: s.cancel((z - z.subs(W, 0)) / W))
    assert matrix.row_join(coeffs(shift)).rank() == 4
assert matrix.row_join(coeffs(u * W**2)).rank() == 5
print("PASS: binary identity, four invariant numerator columns, four exact limits,")
print("      rank four, backward-shift invariance, and failure of gradedness.")
