"""Exact checks. Run with `heavy python3 verify_difference_kernel_minors.py`.

No floating-point arithmetic is used. Bareiss elimination checks the Bose
minor. Fixed-point rational intervals independently check it and check the
finite Boolean-difference weight minor using positive beta-function sums.
This is an external arithmetic certificate, not a Lean declaration.
"""

import hashlib
import json
import math
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.set_int_max_str_digits(0)
BASE = Path(__file__).resolve().parent
B = [8, 9, 10, 12, 13, 15, 17, 19, 22, 25, 28, 32, 36, 41, 46, 52, 59,
     67, 76, 86, 97, 110, 125]
Q = [2518, 2259, 2053, 1887, 1751, 1639, 1547, 1470, 1405, 1350, 1303,
     1263, 1229, 1199, 1174, 1152, 1133, 1117, 1102, 1090, 1079, 1069, 1061]
DEN = 1000
R = 1000
PRECISION = 1400
UNIT = 1 << PRECISION


class Interval:
    """Inclusive endpoints, each in units of 2**(-PRECISION)."""

    def __init__(self, lo, hi):
        assert lo <= hi
        self.lo, self.hi = lo, hi

    @staticmethod
    def ratio(n, d=1):
        assert d > 0
        return Interval(n * UNIT // d, -((-n * UNIT) // d))

    def __add__(self, other):
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-other)

    def __mul__(self, other):
        products = [a * b for a in (self.lo, self.hi)
                    for b in (other.lo, other.hi)]
        return Interval(min(products) // UNIT, -((-max(products)) // UNIT))

    def inverse(self):
        assert self.lo > 0 or self.hi < 0, "division interval includes zero"
        return Interval(UNIT * UNIT // self.hi,
                        -((-UNIT * UNIT) // self.lo))

    def __truediv__(self, other):
        return self * other.inverse()


def determinant_interval(matrix):
    """Outward-rounded Gaussian elimination, with certified nonzero pivots."""
    a = [list(row) for row in matrix]
    n = len(a)
    result = Interval.ratio(1)
    for k in range(n):
        p = max(range(k, n), key=lambda i: abs(a[i][k].lo + a[i][k].hi))
        if p != k:
            a[k], a[p] = a[p], a[k]
            result = -result
        pivot = a[k][k]
        assert pivot.lo > 0 or pivot.hi < 0
        result = result * pivot
        for i in range(k + 1, n):
            factor = a[i][k] / pivot
            for j in range(k + 1, n):
                a[i][j] = a[i][j] - factor * a[k][j]
            a[i][k] = Interval.ratio(0)
    return result


def bose_integer_determinant():
    a = []
    for b in B:
        ds = [q**b - DEN**b for q in Q]
        assert all(d > 0 for d in ds)
        common = math.lcm(*ds)
        row = [DEN**b * (common // d) for d in ds]
        gcd = math.gcd(*row)
        assert gcd > 0
        a.append([x // gcd for x in row])
    previous, sign = 1, 1
    for k in range(len(a) - 1):
        if a[k][k] == 0:
            p = next(i for i in range(k + 1, len(a)) if a[i][k])
            a[k], a[p] = a[p], a[k]
            sign = -sign
        pivot = a[k][k]
        for i in range(k + 1, len(a)):
            for j in range(k + 1, len(a)):
                value, remainder = divmod(
                    a[i][j] * pivot - a[i][k] * a[k][j], previous)
                assert remainder == 0
                a[i][j] = value
            a[i][k] = 0
        previous = pivot
    return sign * a[-1][-1]


def geometric_product_except(skip):
    """Coefficients of product_{i != skip}(1+z+...+z**(B[i]-1))."""
    coefficients = [1]
    for i, b in enumerate(B):
        if i == skip:
            continue
        result, total = [], 0
        for k in range(len(coefficients) + b - 1):
            if k < len(coefficients):
                total += coefficients[k]
            if k >= b:
                total -= coefficients[k - b]
            result.append(total)
        coefficients = result
    assert all(x > 0 for x in coefficients)
    return coefficients


def difference_matrix():
    """F_i(D)/Beta(D,R+r+1), with F_i=b_i J_i and D=1000R/(Q_j-1000)."""
    n, m = len(B), R + len(B)
    polynomials = [geometric_product_except(i) for i in range(n)]
    matrix = [[None] * n for _ in range(n)]
    for j, q in enumerate(Q):
        d = Interval.ratio(DEN * R, q - DEN)
        for i, b in enumerate(B):
            factor = Interval.ratio(b, m) * d
            for k in range(1, b):
                factor = factor * ((d + Interval.ratio(k)) /
                                   (d + Interval.ratio(m + k)))
            value, term = Interval.ratio(0), Interval.ratio(1)
            for k, coefficient in enumerate(polynomials[i]):
                value = value + Interval.ratio(coefficient) * term
                term = term * ((d + Interval.ratio(b + k)) /
                               (d + Interval.ratio(b + m + k)))
            matrix[i][j] = factor * value
        column_scale = matrix[0][j]
        assert column_scale.lo > 0
        for i in range(n):
            matrix[i][j] = matrix[i][j] / column_scale
    return matrix


def encode_interval(interval):
    return {"lower_numerator": interval.lo, "upper_numerator": interval.hi,
            "common_denominator_power_of_two": PRECISION}


def main():
    assert all(a < b for a, b in zip(B, B[1:]))
    assert all(a > b > DEN for a, b in zip(Q, Q[1:]))
    determinant = bose_integer_determinant()
    assert determinant < 0
    print("Bose minor: exact integer determinant negative", flush=True)
    bose = determinant_interval([[Interval.ratio(DEN**b, q**b - DEN**b)
                                  for q in Q] for b in B])
    assert bose.hi < 0
    print("Bose minor: independent rational interval determinant negative", flush=True)
    difference = determinant_interval(difference_matrix())
    assert difference.hi < 0
    print("Finite difference minor: rational interval determinant negative", flush=True)
    result = {
        "status": "PASS",
        "checked_utc": datetime.now(timezone.utc).isoformat(),
        "method": "Exact integer Bareiss and independent outward rational interval elimination",
        "floating_point_used": False,
        "lean_checked": False,
        "b": B, "q_numerators": Q, "q_denominator": DEN,
        "dummy_count": R, "total_difference_order": R + len(B),
        "integer_determinant_bit_length": abs(determinant).bit_length(),
        "integer_determinant_sha256": hashlib.sha256(str(determinant).encode()).hexdigest(),
        "bose_determinant_interval": encode_interval(bose),
        "normalized_difference_determinant_interval": encode_interval(difference),
        "verifier_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "main_target_proved": False,
    }
    (BASE / "difference-kernel-minors-audit.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
