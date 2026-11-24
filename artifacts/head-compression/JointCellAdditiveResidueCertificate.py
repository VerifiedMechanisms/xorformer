#!/usr/bin/env python3
"""Exact finite scalar certificate, not an original-model head compiler.

All comparisons use fractions.  Decimal values in the JSON are explanatory
only and are never used by the verification.
"""

from fractions import Fraction
from itertools import product
import json
from pathlib import Path


def determinant(matrix):
    matrix = [list(map(Fraction, row)) for row in matrix]
    answer = Fraction(1)
    for i in range(len(matrix)):
        pivot = next((j for j in range(i, len(matrix)) if matrix[j][i]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != i:
            matrix[i], matrix[pivot] = matrix[pivot], matrix[i]
            answer = -answer
        diagonal = matrix[i][i]
        answer *= diagonal
        for j in range(i + 1, len(matrix)):
            scale = matrix[j][i] / diagonal
            for k in range(i + 1, len(matrix)):
                matrix[j][k] -= scale * matrix[i][k]
    return answer


def main():
    path = Path(__file__).with_name("joint-cell-additive-residue-certificate.json")
    data = json.loads(path.read_text())
    blocks = data["blocks"]
    assert blocks == [[0, 1, 139], [0, 23, 20737]]
    points = list(product(range(3), repeat=2))
    poles = [blocks[0][i] + blocks[1][j] for i, j in points]
    features = [
        [1, int(i == 1) - int(i == 0), int(i == 2) - int(i == 0),
         int(j == 1) - int(j == 0), int(j == 2) - int(j == 0)]
        for i, j in points
    ]
    coefficients = [Fraction(*pair) for pair in data["coefficients"]]
    residues = [sum(a * b for a, b in zip(coefficients, row)) for row in features]
    previous = Fraction(0)
    verified_signs = []
    for expected in data["evaluations"]:
        point = Fraction(*expected["point"])
        assert previous < point
        previous = point
        assert all(point + pole > 0 for pole in poles)
        value = sum(residue / (point + pole) for residue, pole in zip(residues, poles))
        sign = (value > 0) - (value < 0)
        assert sign == expected["sign"]
        verified_signs.append(sign)
    assert verified_signs == [-1, 1, -1, 1, -1, 1]
    # Positive row factors convert this determinant to the order-five
    # derivative Wronskian without changing its sign.
    for point, expected_sign in [(200, -1), (250, 1)]:
        matrix = [[sum(Fraction(row[j], (point + pole) ** (k + 1))
                       for pole, row in zip(poles, features))
                   for j in range(5)] for k in range(5)]
        value = determinant(matrix)
        assert (value > 0) - (value < 0) == expected_sign
    # Optimized weak-negative extension on the two one-hot plane blocks.
    margin = sum(3 * block[2] - 2 * block[1] for block in blocks)
    assert margin == 62580
    assert all(Fraction(*row["point"]) < margin for row in data["evaluations"])
    print("Exact rational verification passed: six alternating signs, Wronskian reversal.")
    print("Not an admissible compiler: all sample gaps are below the 62580 cube margin.")


if __name__ == "__main__":
    main()
