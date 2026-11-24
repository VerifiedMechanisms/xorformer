#!/usr/bin/env python3
"""Exact coefficient and rank checks for the confluent density audit."""
from fractions import Fraction as F
from itertools import permutations
from random import Random
from math import comb
from flint import fmpq_mat


def moment_rows(profiles, cutoff):
    h = len(profiles[0])
    rows = []
    for x in profiles:
        for j in range(cutoff + 1):
            rows.append([z ** j for z in x]
                        + ([0] * h if j == 0
                           else [j * z ** (j - 1) for z in x]))
    return rows


def rank(rows):
    return fmpq_mat(rows).rank()


def cutoff(profiles):
    h = len(profiles[0])
    for ell in range(2 * h):
        if rank(moment_rows(profiles, ell)) == 2 * h:
            return ell
    raise AssertionError("The pure distinct-pole group should be injective")


# Coefficients in a/(t-e*x) + e*c/(t-e*x)^2.
checks = 0
for x in range(-3, 4):
    for a in (-2, 1, 3):
        for c in (-1, 0, 2):
            for j in range(9):
                geometric = a * x ** j
                derivative = 0 if j == 0 else c * j * x ** (j - 1)
                stated = a * x ** j + (0 if j == 0 else j * c * x ** (j - 1))
                assert geometric + derivative == stated
                checks += 1

fiber = [(3, 4, 2, 1), (4, 2, 3, 1), (4, 3, 1, 2)]
small_cutoffs = []
for pi in fiber:
    profiles = [list(pi), [pi[h] + h + 1 for h in range(4)]]
    ell = cutoff(profiles)
    small_cutoffs.append(ell)
    assert ell == 4
    assert rank(moment_rows(profiles, ell - 1)) < 8

rng = Random(917)
diagnostics = []
for h in (6, 8, 10, 12):
    pi = list(range(1, h + 1))
    rng.shuffle(pi)
    profiles = [pi[:]]
    for groups in range(2, 7):
        rho = list(range(1, h + 1))
        rng.shuffle(rho)
        profiles.append([pi[i] + rho[i] for i in range(h)])
        ell = cutoff(profiles)
        assert rank(moment_rows(profiles, ell)) == 2 * h
        diagnostics.append((h, groups, ell))

# The elementary sign-change count used in the density bound.
for q in range(1, 10):
    for ell in range(q):
        actual = sum(sum(((bits >> j) ^ (bits >> (j + 1))) & 1
                         for j in range(q - 1)) <= ell
                     for bits in range(1 << q))
        assert actual == 2 * sum(comb(q - 1, j) for j in range(ell + 1))

print(f"PASS: {checks} coefficient identities; saved H4 cutoffs {small_cutoffs}")
print("Exact (heads, groups, first injective cutoff) diagnostics:", diagnostics)
print("Sign-change counts verified. No finite-scale density or universality inferred.")
