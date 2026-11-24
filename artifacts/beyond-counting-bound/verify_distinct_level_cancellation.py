"""Check exact Jacobian ranks for the written analytic deformation proof.

This does not numerically solve or certify the nonlinear moment equations.
"""

from pathlib import Path
import hashlib
import json
from math import isqrt


def rref_mod(matrix, prime):
    matrix = [row[:] for row in matrix]
    pivots = []
    row_index = 0
    for column in range(len(matrix[0])):
        pivot = next((r for r in range(row_index, len(matrix)) if matrix[r][column]), None)
        if pivot is None:
            continue
        matrix[row_index], matrix[pivot] = matrix[pivot], matrix[row_index]
        inverse = pow(matrix[row_index][column], -1, prime)
        matrix[row_index] = [value * inverse % prime for value in matrix[row_index]]
        for r in range(len(matrix)):
            if r != row_index:
                coefficient = matrix[r][column]
                if coefficient:
                    matrix[r] = [(value - coefficient * base) % prime
                                 for value, base in zip(matrix[r], matrix[row_index])]
        pivots.append(column)
        row_index += 1
        if row_index == len(matrix):
            break
    return matrix, pivots


def main():
    prime = 1000000007
    assert all(prime % divisor for divisor in range(2, isqrt(prime) + 1))
    cases = []
    for q, m in ((4, 2), (4, 3), (4, 5), (4, 9), (8, 10), (8, 20), (8, 35)):
        assert m < q * (q + 1) // 2
        levels = [3 ** i for i in range(1, q + 1)]
        assert len({levels[i] + levels[j] for i in range(q) for j in range(i, q)}) == q * (q + 1) // 2
        rows = []
        for s in range(2, m + 2):
            row = []
            for u_i in levels:
                total = sum(pow(u_i + u_l, s - 1, prime) for u_l in levels) % prime
                row.extend(2 * s * (q * pow(u_i + u_j, s - 1, prime) - total) % prime
                           for u_j in levels)
            rows.append(row)
        _, all_pivots = rref_mod(rows, prime)
        assert len(all_pivots) == m
        rref, pivots = rref_mod(rows[:-1], prime)
        assert len(pivots) == m - 1
        forbidden = 0
        for i in range(q):
            for j in range(q):
                for ell in range(j + 1, q):
                    functional = [0] * (q * q)
                    functional[i * q + j] = 1
                    functional[i * q + ell] = prime - 1
                    for row_index, pivot in enumerate(pivots):
                        coefficient = functional[pivot]
                        if coefficient:
                            functional = [(value - coefficient * rref[row_index][col]) % prime
                                          for col, value in enumerate(functional)]
                    assert any(functional)
                    forbidden += 1
        cases.append({"m": m, "q": q, "H": q * q, "low_rank": m - 1,
                      "rank_with_next_moment": m, "collision_functionals_checked": forbidden})
    root = Path(__file__).resolve().parent
    report = {
        "scope": "Exact finite Jacobian checks; analytic deformation is a written proof, not a numerical certificate",
        "method": "Multiply the rational Jacobian by q; full row rank modulo the trial-division-verified prime proves full row rank over the rationals. Augmented row ranks certify tangent exclusions.",
        "prime": prime,
        "cases": cases,
        "files": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                  for name in ("distinct-level-deep-cancellation.md", Path(__file__).name)},
    }
    (root / "distinct-level-deep-cancellation-audit.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
