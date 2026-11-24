"""Exact replay of the fixed-direction flattening obstruction.

No numerical optimizer is used in verification. This is not a worst-case
head-count lower bound or an obstruction to changing directions.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json


def main():
    directory = Path(__file__).resolve().parent
    source = directory / "homothetic-flattening-certificate.json"
    data = json.loads(source.read_text())
    assert data["n"] == 4 and data["flattening_constant"] == 100
    points = [[(j >> i) & 1 for i in range(4)] for j in range(16)]
    slopes = data["slopes"]
    assert all(b > 0 for row in slopes for b in row)
    labels = data["labels"]
    coefficients = data["coefficients"]
    limit_rows, flat_rows = [], []
    for j, x in enumerate(points):
        u, v = [sum(b * a for b, a in zip(row, x)) for row in slopes]
        score = Q(coefficients[0])
        for h, den in enumerate([1 + u, 1 + v]):
            score += Q(sum(coefficients[1 + 4 * h + i] * x[i] for i in range(4)), den)
        assert score == Q(data["scores"][j]) and score * labels[j] > 0
        limit_rows.append([1] + x + [a * (v - u) for a in x])
        flat_rows.append([(100 + u) * (100 + v)] +
                         [a * (100 + v) for a in x] + [a * (v - u) for a in x])
    for rows, weights in [(limit_rows, data["positive_dual"]),
                          (flat_rows, data["flattened_positive_dual_cleared"])]:
        assert all(Q(w) > 0 for w in weights)
        for k in range(9):
            assert sum(Q(weights[j]) * labels[j] * rows[j][k] for j in range(16)) == 0
    minor = [limit_rows[j] for j in data["limit_minor_rows"]]
    inverse = [[Q(a) for a in row] for row in data["limit_minor_inverse"]]
    for i in range(9):
        for j in range(9):
            assert sum(inverse[i][k] * minor[k][j] for k in range(9)) == (i == j)
    result = {
        "status": "PASS",
        "strict_scores": 16,
        "positive_certificate_entries": 32,
        "annihilation_identities": 18,
        "inverse_entries": 81,
        "certificate_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "scope": "Exact finite arithmetic. The general continuity argument is a written proof.",
        "main_target_proved": False,
    }
    (directory / "homothetic-flattening-rational-audit.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
