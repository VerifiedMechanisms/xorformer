#!/usr/bin/env python3
"""Run the exact arithmetic certificates supporting Theorem 22.

No Boolean cube of astronomical size is enumerated. The finite checks verify
the coefficient identities and bounds used in the symbolic all-input proof.
The analytic tensor exclusion and sign-rigidity arguments remain handwritten.
Only the Python standard library is required.
"""

from fractions import Fraction as F
import importlib.util
import json
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
    construction = json.loads((ROOT / 'explicit_separation/construction.json').read_text())
    assert construction['format_version'] == 1
    assert construction['replication_count'] == {'base': 2, 'exponent': 400000}
    assert construction['input_count'] == {'multiplier': 14, 'factor': 'replication_count'}
    assert construction['indices'] == {
        'head_h': [0, 1, 2], 'group_i': {'first': 1, 'last': 14},
        'copy_r': {'first': 0, 'last': 'm-1'}, 'flat_bit_index': '(i-1)*m+r'}
    assert construction['centered_group_mean'] == 'z_i=(sum_{r=0}^{m-1}(2*x_{i,r}-1))/m'
    assert construction['s_denominator'] == 10000
    assert construction['b_denominator'] == w
    assert int(construction['grid_polynomial_denominator_base']) == denominator_base
    assert construction['integer_s_coefficients'] == [
        [i**h for i in range(1, 15)] for h in range(3)]
    assert construction['integer_b_coefficients'] == [
        [32 * i**(h + 3) - 2**(2 - h) * 15**(h + 3) for i in range(1, 15)]
        for h in range(3)]
    assert [[F(x) for x in row] for row in construction['base_s']] == s
    assert [[F(x) for x in row] for row in construction['base_b']] == b
    assert construction['linear_forms'] == {
        'S_h': 'sum_{i=1}^{14} base_s[h][i-1]*z_i',
        'B_h': 'sum_{i=1}^{14} base_b[h][i-1]*z_i', 'D_h': '1+B_h'}
    assert construction['cleared_polynomial']['formula'] == (
        'F=S_0*D_1*D_2+S_1*D_0*D_2+S_2*D_0*D_1')
    assert construction['cleared_polynomial']['terms'] == [
        {'numerator_head': h, 'denominator_heads': [j for j in range(3) if j != h]}
        for h in range(3)]
    assert construction['function'] == {'true_iff': 'F(z)>0', 'false_iff': 'F(z)<=0'}
    assert construction['readout_constant'] == '-1/(16*A*m^3)'
    assert construction['strict_margin_lower_bound'] == '1/(16*A*m^3)'
    for h, atom in enumerate(construction['pure_atoms']):
        assert atom['head'] == h
        assert [F(x) for x in atom['token_zero_weight_base']] == [
            si - bi for si, bi in zip(s[h], b[h])]
        assert [F(x) for x in atom['token_one_weight_base']] == [
            si + bi for si, bi in zip(s[h], b[h])]
        assert F(atom['query_weight']) == 1 - sum(s[h])
        assert F(atom['query_numerator']) == -sum(b[h])
        assert F(atom['token_zero_value']) == -1
        assert F(atom['token_one_value']) == 1
        assert atom['input_weight_replication_rule'] == (
            'each stored base weight is divided by m at every copy r')
    assert len(construction['pure_atoms']) == 3
    vanilla = construction['vanilla_seven_upper']
    assert vanilla['epsilon'] == '1/(16*A*m^3)'
    assert vanilla['a'] == 'epsilon/4096'
    assert vanilla['R'] == '1+sum_{i=1}^{14}sum_{r=0}^{m-1}x_{i,r}'
    assert vanilla['U'] == ['S_0-epsilon*D_0', 'S_1', 'S_2']
    assert vanilla['denominator_rule'] == 'R+a*sum(D_h for h in denominator_subset)'
    assert vanilla['numerator_rule'] == (
        'sum(numerator_U_coefficients[h]*U_h for h in [0,1,2])')
    assert vanilla['readout_constant'] == '0'
    # Collect the three reciprocal second differences by denominator subset.
    collected = {}
    for h in range(3):
        j, k = [index for index in range(3) if index != h]
        for subset, sign in [((), 1), ((j,), -1), ((k,), -1), ((j, k), 1)]:
            vector = collected.setdefault(subset, [0, 0, 0])
            vector[h] += sign
    assert len(vanilla['heads']) == 7
    assert {tuple(head['denominator_subset']): head['numerator_U_coefficients']
            for head in vanilla['heads']} == collected
    a = epsilon / 4096
    assert F(576, 4096) < F(1, 4)
    assert epsilon < F(1, 16)
    assert 4 * a < 1
    for sh, bh in zip(s, b):
        assert all(si > abs(bi) for si, bi in zip(sh, bh))
        assert sum(sh) < 1
        assert sum(sh) < F(1, 4)
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
    print('  construction.json matches every integer coefficient and rational atom parameter')
    print('  seven explicit vanilla fractions use a=epsilon/4096; all bound constants pass')
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
