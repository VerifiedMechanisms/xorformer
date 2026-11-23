#!/usr/bin/env python3
"""Exact rational replay of the two-head normalized-energy obstruction.

No optimizer or numerical differentiation is used. The square-root norm is
removed algebraically from the normalized differential equations.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path


def dot(a, b):
    return sum((x*y for x, y in zip(a, b)), F(0))


def check(t):
    assert 0 < t <= 1
    points = [(0, 0), (1, 0), (0, 1), (1, 1)]
    c = 1-t/2
    slopes = [(F(1), F(1)), (1/c, (1+t)/c)]
    numerators = [[F(x)-F(1, 2) for x, y in points],
                  [-(F(x)-F(1, 2))/c for x, y in points]]
    tables = []
    derivatives = []
    second = [[None for j in range(4)] for i in range(4)]
    metric = [[F(0) for j in range(4)] for i in range(4)]
    drift = []
    for h in range(2):
        b = slopes[h]
        assert min(b) > 0
        D = [1+dot(b, x) for x in points]
        assert min(D) > 0
        T = [a/d for a, d in zip(numerators[h], D)]
        tables.append(T)
        for i in range(2):
            derivatives.append([-a*x[i]/d**2 for a, x, d in zip(numerators[h], points, D)])
            drift.append(2*b[i])
            for j in range(2):
                metric[2*h+i][2*h+j] = (b[i] if i == j else 0)+b[i]*b[j]
                second[2*h+i][2*h+j] = [2*a*x[i]*x[j]/d**3
                    for a, x, d in zip(numerators[h], points, D)]
    for i in range(4):
        for j in range(4):
            if second[i][j] is None:
                second[i][j] = [F(0)]*4
    S = [tables[0][x]+tables[1][x] for x in range(4)]
    expected = [t/(4-2*t), -t/(16-4*t), -t/(16+4*t), t/(36+6*t)]
    assert S == expected
    assert [v > 0 for v in S] == [True, False, False, True]
    G = dot(S, S)
    assert 0 < G <= t*t
    g = derivatives[0]
    assert g == [F(0), F(-1, 8), F(0), F(-1, 18)]
    gram = G*dot(g, g)-dot(S, g)**2
    minor_sum = (S[0]/8)**2+(S[0]/18)**2+(S[2]/8)**2+(
        S[1]/18-S[3]/8)**2+(S[2]/18)**2
    assert gram == minor_sum
    assert gram >= t*t/1024
    coordinate_energy = gram/G**2
    lower = 1/(1024*t*t)
    assert coordinate_energy >= lower
    log_norm_grad = [dot(S, d)/G for d in derivatives]
    # These arrays equal sqrt(G) times derivatives of U=S/sqrt(G).
    normalized_first = [[derivatives[i][x]-S[x]*log_norm_grad[i]
                         for x in range(4)] for i in range(4)]
    normalized_second = [[[second[i][j][x]
        - derivatives[i][x]*log_norm_grad[j]
        - derivatives[j][x]*log_norm_grad[i]
        - S[x]*(dot(derivatives[i], derivatives[j])+dot(S, second[i][j]))/G
        + 3*S[x]*log_norm_grad[i]*log_norm_grad[j]
        for x in range(4)] for j in range(4)] for i in range(4)]
    potential = sum((metric[i][j]*dot(normalized_first[i], normalized_first[j])/G
                     for i in range(4) for j in range(4)), F(0))
    assert potential >= coordinate_energy
    corrected_drift = [drift[i]+2*dot(metric[i], log_norm_grad) for i in range(4)]
    for x in range(4):
        unnormalized = sum((metric[i][j]*second[i][j][x]
                            for i in range(4) for j in range(4)), F(0))
        unnormalized += sum((drift[i]*derivatives[i][x] for i in range(4)), F(0))
        assert unnormalized == 0
        normalized = sum((metric[i][j]*normalized_second[i][j][x]
                          for i in range(4) for j in range(4)), F(0))
        normalized += sum((corrected_drift[i]*normalized_first[i][x] for i in range(4)), F(0))
        normalized += potential*S[x]
        assert normalized == 0
    return {"t": str(t), "norm_squared": str(G),
            "scaled_coordinate_energy": str(t*t*coordinate_energy),
            "scaled_full_potential": str(t*t*potential)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    parameters = sorted({F(1, k) for k in range(1, 25)} | {F(1, 2**k) for k in range(1, 81)})
    records = [check(t) for t in parameters]
    audit = {"status": "PASS", "cases": len(records), "cube_entries": 4*len(records),
             "arithmetic": "fractions.Fraction only", "records": records,
             "main_target_proved": False,
             "scope": "Exact finite replay; general divergence proof is separate."}
    args.output.write_text(json.dumps(audit, indent=2)+"\n")
    print(json.dumps({k: v for k, v in audit.items() if k != "records"}))


if __name__ == "__main__":
    main()
