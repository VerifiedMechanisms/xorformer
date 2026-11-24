"""Independent exact checks for the written sparse-sign compiler obstruction."""
from fractions import Fraction as F
from itertools import permutations, product
from math import comb, prod
from pathlib import Path
import datetime
import json


def sign(x):
    return (x > 0) - (x < 0)


def fwht(values):
    out = list(values)
    step = 1
    while step < len(out):
        for start in range(0, len(out), 2 * step):
            for j in range(start, start + step):
                a, b = out[j], out[j + step]
                out[j], out[j + step] = a + b, a - b
        step *= 2
    return out


checks = {}
paths = 0
for m in range(7):
    for trial in range(9):
        u = [F(((7 * i + 3 * trial) % 11) - 5, (i % 3) + 1) for i in range(m)]
        d = 1 + sum(map(abs, u))
        lhs = F(0)
        for bits in product((0, 1), repeat=m):
            den = d + sum(v for v, b in zip(u, bits) if b)
            assert den > 0
            lhs += F((-1) ** sum(bits), 1) / den
        rhs = F(0)
        for pi in permutations(range(m)):
            t, term = d, 1 / d
            for i in pi:
                t += u[i]
                assert t > 0
                term /= t
            rhs += term
            paths += 1
        rhs *= prod(u)
        assert lhs == rhs
        assert sign(lhs) == sign(prod(u))
checks['finite_difference'] = {'instances': 63, 'positive_paths_checked': paths}

central = F(1)
for r in range(129):
    assert central == F(comb(2 * r, r), 4 ** r)
    assert central ** 2 * (r + 1) <= 1
    assert 4 * (r + 1) ** 3 - (2 * r + 1) ** 2 * (r + 2) == 3 * r + 2
    central *= F(2 * r + 1, 2 * r + 2)
checks['central_binomial'] = {'instances': 129}

spectra = []
for m in range(1, 14, 2):
    labels = [sign(m - 2 * x.bit_count()) for x in range(2 ** m)]
    spectrum = fwht(labels)
    maximum = 2 * comb(m - 1, (m - 1) // 2)
    assert spectrum[0] == 0
    assert max(map(abs, spectrum)) == maximum
    assert all(v == 0 for s, v in enumerate(spectrum) if s.bit_count() % 2 == 0)
    spectra.append({'block_bits': m, 'largest_unnormalized_coefficient': maximum})
checks['majority_spectra'] = spectra

triples = []
for m in (1, 3, 5):
    mask = (1 << m) - 1
    labels = [prod(sign(m - 2 * ((x >> (j * m)) & mask).bit_count()) for j in range(3))
              for x in range(1 << (3 * m))]
    spectrum = fwht(labels)
    maximum = (2 * comb(m - 1, (m - 1) // 2)) ** 3
    assert max(map(abs, spectrum)) == maximum
    triples.append({'bits': 3 * m, 'largest_unnormalized_coefficient': maximum,
                    'density_lower_bound': str(F(len(labels), maximum))})
checks['product_spectra'] = triples

scores = []
for m in (1, 3, 5, 7):
    margins, flat_margins = [], []
    epsilon = F(1, 100)
    delta = epsilon / (1 + 9 * m)
    for counts in product(range(m + 1), repeat=3):
        A, u, v = (m - 2 * t for t in counts)
        d = 1 + 2 * m + counts[0] + 3 * counts[1] + 3 * counts[2]
        den = (d, d + u, d + v, d + u + v)
        assert min(den) > 0
        signs = (1, -1, -1, 1)
        s = sum(F(e * A, t) for e, t in zip(signs, den))
        explicit = F(A * u * v * (2 * d + u + v), prod(den))
        assert s == explicit
        label = sign(A * u * v)
        assert label * s > 0
        flat_den = [1 + delta * t for t in den]
        assert all(1 <= t <= 1 + epsilon for t in flat_den)
        flat = sum(F(e * A, 1) / t for e, t in zip(signs, flat_den))
        assert label * flat > 0
        margins.append(label * s)
        flat_margins.append(label * flat)
    scores.append({'block_bits': m, 'count_classes': len(margins),
                   'minimum_margin': str(min(margins)),
                   'conditioned_minimum_margin': str(min(flat_margins)),
                   'denominator_upper_bound': str(1 + epsilon)})
checks['four_head_scores'] = scores

mobius_count = 0
for n in range(10):
    coeff = [(-1) ** x.bit_count() * (1 + (37 * x) % 97) for x in range(1 << n)]
    for i in range(n):
        for s in range(1 << n):
            if s & (1 << i):
                coeff[s] -= coeff[s ^ (1 << i)]
    assert all((-1) ** s.bit_count() * c > 0 for s, c in enumerate(coeff))
    mobius_count += len(coeff)
checks['parity_mobius'] = {'dimensions': 10, 'nonzero_coefficients_checked': mobius_count}

result = {'status': 'PASS', 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'method': 'Independent integer arithmetic and fractions; no optimizer or Lean output used.',
          'checks': checks, 'main_target_proved': False,
          'scope': 'Finite checks of complete written arguments; not an asymptotic head lower bound.'}
out = Path(__file__).with_name('sparse-sign-compiler-rational-audit.json')
out.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'checks': list(checks), 'output': str(out)}))
