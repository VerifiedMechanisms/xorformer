#!/usr/bin/env python3
"""Exact tangent checks for the written local positive moment-split theorem."""
from fractions import Fraction as F
from itertools import product
import json


def polynomial(roots, x):
    value = F(1)
    for root in roots:
        value *= x - root
    return value


def derivative(roots, x):
    return sum((polynomial(roots[:i] + roots[i + 1:], x)
                for i in range(len(roots))), F(0))


words = identities = moments = 0
for M in range(1, 9):
    poles = [F(h + 1, 10 * M) for h in range(M)]
    weights = [F(h + 1) for h in range(M)]
    queries = [1 + F(j + 1, M) for j in range(M)]
    for sigma in product((-1, 1), repeat=M):
        roots = [(queries[j] + queries[j + 1]) / 2 for j in range(M - 1)
                 if sigma[j] != sigma[j + 1]]
        scale = F(sigma[0] * (-1) ** len(roots))
        alpha, beta = [], []
        for h, pole in enumerate(poles):
            others = poles[:h] + poles[h + 1:]
            qp = polynomial(others, pole)
            qpp = 2 * derivative(others, pole)
            n = scale * polynomial(roots, pole)
            np = scale * derivative(roots, pole)
            beta.append(n / qp ** 2)
            alpha.append(np / qp ** 2 - n * qpp / qp ** 3)
            assert sigma[0] * beta[-1] / weights[h] > 0
        for k in range(M):
            assert sum((alpha[h] * poles[h] ** k +
                        (k * beta[h] * poles[h] ** (k - 1) if k else 0)
                        for h in range(M)), F(0)) == 0
            moments += 1
        for j, t in enumerate(queries):
            value = sum((alpha[h] / (t - poles[h]) +
                         beta[h] / (t - poles[h]) ** 2 for h in range(M)), F(0))
            expected = scale * polynomial(roots, t) / polynomial(poles, t) ** 2
            assert value == expected and sigma[j] * value > 0
            identities += 1
        words += 1
print(json.dumps(dict(sign_words=words, rational_identities=identities,
                      vanishing_moments=moments,
                      status='tangent identities only; nonlinear existence is written IFT proof')))
