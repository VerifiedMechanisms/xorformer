"""Exact four-bit, two-head weak-limit layer certificate."""

from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json


def poly_mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        for j, v in enumerate(b):
            out[i + j] += u * v
    return out


def atom_parameters(a0, a, b0, b):
    # Delta zero, scale alpha-1 large enough to leave gamma positive.
    scale = 2 * sum(b) / b0
    rho = [v / scale for v in b]
    alpha = 1 + scale
    gamma = b0 - sum(rho)
    m = [u / v for u, v in zip(a, b)]
    eta = a0 - sum(r * v for r, v in zip(rho, m))
    assert alpha > 0 and gamma > 0 and all(r > 0 for r in rho)
    return eta, gamma, alpha, rho, m


def atom_value(params, bits):
    eta, gamma, alpha, rho, m = params
    wt = [r * (alpha if x else 1) for r, x in zip(rho, bits)]
    return (eta + sum(w * v for w, v in zip(wt, m))) / (gamma + sum(wt))


rows, orders = [], set()
for bits in product([0, 1], repeat=4):
    x0, x1, x2, x3 = bits
    numerator = [Q(0)] + poly_mul([Q(x0), Q(x1), Q(1)],
                                 [Q(x2), Q(0), Q(0), Q(x3), Q(0), Q(0), Q(1)])
    order = next(i for i, a in enumerate(numerator) if a)
    orders.add(order)
    D = 1 + sum(bits)
    assert numerator[order] == 1
    for t in [Q(1), Q(1, 2), Q(1, 10)]:
        A = t ** 2 + x0 + t * x1
        B = t ** 6 + x2 + t ** 3 * x3
        score = A / D - A / (D + t * B)
        assert score == t * A * B / (D * (D + t * B)) > 0
        numerator_slopes = [Q(1), t, Q(0), Q(0)]
        first = atom_parameters(t ** 2, numerator_slopes, Q(1), [Q(1)] * 4)
        second = atom_parameters(-t ** 2, [-u for u in numerator_slopes],
                                 1 + t ** 7, [Q(1), Q(1), 1 + t, 1 + t ** 4])
        assert atom_value(first, bits) + atom_value(second, bits) == score
    rows.append({"bits": bits, "order": order, "leading_coefficient": str(Q(1, D * D))})
assert orders == set(range(1, 10))
report = {"arithmetic": "exact fractions.Fraction", "dimension": 4, "heads": 2,
          "orders": sorted(orders), "truth_table": "constant true", "inputs": rows}
Path(__file__).with_name("weak_limit_layer_certificate.json").write_text(json.dumps(report, indent=2) + "\n")
print("Verified all nine vanishing orders for two admissible heads on the four-bit cube.")
