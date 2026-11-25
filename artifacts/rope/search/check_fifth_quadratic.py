"""Exact quadratic sign certificate at replication five.

The certificate gives threshold degree at most two, not a two-head model.
The six aggregate integer coordinates are odd numbers from -15 through 15.
All arithmetic after the explicit overflow bound uses signed int64 arrays.
"""

import itertools
import json
from pathlib import Path

import numpy as np


def verify():
    m = 5
    rows = np.array(list(itertools.product(range(-15, 16, 2), repeat=3)), dtype=np.int64)
    b = rows[None, :, :]
    # |L| <= 315, |N_i| <= 210, |z_i| <= 30, D_i <= 1030.
    assert 3*210*1030**2 < 2**63
    assert 2016*315 + 2*315*90 + 3*210*30 < 2**63
    source_zeros = quadratic_zeros = disagreements = 0
    minimum_absolute_quadratic = None
    for start in range(0, len(rows), 32):
        a = rows[start:start+32, None, :]
        total = a.sum(axis=2)+b.sum(axis=2)
        linear = 4*a.sum(axis=2)+3*b.sum(axis=2)
        z = a-b
        numerator = 2*(total[:, :, None]+a)
        denominator = 200*m+z
        source = sum(numerator[:, :, i]*denominator[:, :, (i+1)%3]*denominator[:, :, (i+2)%3]
                     for i in range(3))
        quadratic = 2016*linear + 2*linear*z.sum(axis=2) - (numerator*z).sum(axis=2)
        disagreements += int(np.count_nonzero((source > 0) != (quadratic > 0)))
        source_zeros += int(np.count_nonzero(source == 0))
        quadratic_zeros += int(np.count_nonzero(quadratic == 0))
        chunk_minimum = int(np.min(np.abs(quadratic)))
        if minimum_absolute_quadratic is None or chunk_minimum < minimum_absolute_quadratic:
            minimum_absolute_quadratic = chunk_minimum
    assert disagreements == 0
    return {'replicas': m, 'patterns': len(rows)**2, 'disagreements': disagreements,
            'source_zeros': source_zeros, 'quadratic_zeros': quadratic_zeros,
            'minimum_absolute_quadratic': minimum_absolute_quadratic,
            'coordinates': 'a_i,b_i in {-15,-13,...,15}; A_i=a_i/5,B_i=b_i/5',
            'definitions': {'L': '4*sum(a)+3*sum(b)', 'z_i': 'a_i-b_i',
                            'N_i': '2*(sum(a)+sum(b)+a_i)'},
            'quadratic': '2016*L+2*L*sum(z)-sum_i(N_i*z_i)',
            'scope': 'Exact threshold-degree-two upper certificate, not a two-head representation'}


if __name__ == '__main__':
    result = verify()
    print(json.dumps(result, indent=2))
    Path('artifacts/rope/search/fifth_replication_quadratic.exact.json').write_text(
        json.dumps(result, indent=2)+'\n')
