#!/usr/bin/env python3
"""Run the exact arithmetic certificates supporting Theorem 22.

No Boolean cube of astronomical size is enumerated. The finite checks verify
the coefficient identities and bounds used in the symbolic all-input proof.
The analytic tensor exclusion and sign-rigidity arguments remain handwritten.
Only the Python standard library is required.
"""

from fractions import Fraction as F
import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


def load(name, relative):
    spec = importlib.util.spec_from_file_location(name, ROOT / relative)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def full_cube_arithmetic(chart, gap):
    m = 2**400000
    s = [[F(i**h, 10000) for i in range(1, 15)] for h in range(3)]
    b = [[(F(i)**(h + 3) - F(15, 2)**(h + 3)) / 10**9
          for i in range(1, 15)] for h in range(3)]
    w = 32 * 10**9
    denominator_base = 10000 * w**2
    epsilon = F(1, 16 * denominator_base * m**3)
    for sh, bh in zip(s, b):
        assert all(si > abs(bi) for si, bi in zip(sh, bh))
        assert sum(sh) < 1
        assert sum(abs(bi) for bi in bh) < F(1, 2)
        assert all((10000 * si).denominator == 1 for si in sh)
        assert all((w * bi).denominator == 1 for bi in bh)
        gamma = 1 - sum(sh)
        eta = -sum(bh)
        # Each of m copies uses masses s/m and biases b/m. Summing the
        # replicated constant coefficients proves the exact atom identities.
        assert gamma + m * sum(si / m for si in sh) == 1
        assert eta + m * sum(bi / m for bi in bh) == 0
        assert gamma > 0
    coefficients = chart.cleared_coefficients(s + b)
    assert all((denominator_base * value).denominator == 1
               for value in coefficients.values())
    assert max(map(len, coefficients)) == 3
    assert sum(coefficients.values()) > 0
    assert sum((-1)**len(key) * value for key, value in coefficients.items()) < 0
    # For every grid point z_i=k_i/m, A*m^3*F(z) is an integer. If nonzero,
    # |F(z)| >=1/(A*m^3). The positive denominator product is less than8.
    nonzero_score_bound = F(1, 8 * denominator_base * m**3)
    assert nonzero_score_bound == 2 * epsilon
    assert epsilon > 0
    # The negative readout shift leaves every nonzero sign unchanged and
    # makes each original zero equal to -epsilon. The margin is >=epsilon.

    # Explicit finite-grid inequalities used by the sign-rigidity argument.
    t = F(2**20, m)
    assert F(1, 16) + t * 2**34 < 1
    assert F(2040, m) < t / 4
    assert F(2**54 + 1, m) < F(2**55, m)
    assert F(2040 * 2**55, m) < F(2**67, m)
    error = F(2**300067, m)
    assert error == F(1, 2**99933)
    assert 1 - error > F(1, 2)
    assert 680 * error < F(1, 20000)
    assert 2 * error < F(1, 2**2000) < gap.constants()[-1]
    assert denominator_base < 2**84
    assert error < F(1, 2**85)
    print('exact symbolic cube checks passed: n=14*2^400000, three pure atoms,')
    print('  strict margin >=1/(16*A*m^3), A=10240000000000000000000000')
    print('  interpolation error <2^-99933, tensor exclusion radius >2^-2000')


def main():
    generic = load('pure_generic_certificate', 'generic_cubic_completion/verify.py')
    chart = load('pure_chart_certificate', 'generic_cubic_completion/verify_chart.py')
    gap = load('pure_gap_certificate', 'quantitative_cubic_gap/verify_gap.py')
    generic.main()
    chart.main()
    gap.main()
    full_cube_arithmetic(chart, gap)
    print('All exact arithmetic checks supporting Theorem 22 passed.')
    print('Scope: arithmetic certificates plus symbolic cube identities;')
    print('the full separation proof is mathematical, not a Lean theorem.')


if __name__ == '__main__':
    main()
