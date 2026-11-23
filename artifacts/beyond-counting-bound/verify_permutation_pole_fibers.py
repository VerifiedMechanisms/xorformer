#!/usr/bin/env python3
"""Exact diagnostics for the small-integer matching construction.

No search failure or finite check is used as an asymptotic theorem.
"""
from fractions import Fraction as F
from itertools import permutations, product
from math import factorial
from pathlib import Path
import hashlib
import json


def score(H, ps, selectors, address):
    return sum((F(1, 1 + address + (h + 1) * selectors[0]
                  + sum(H * (p[h] + 1) * bit
                        for p, bit in zip(ps, selectors[1:])))
                for h in range(H)), F(0))


def atom_reciprocal(weights, bits):
    # Literal exact-model parameters, with strictly positive rho and gamma.
    alpha = 1 + 2 * sum(weights)
    rho = [F(w, alpha - 1) for w in weights]
    gamma, eta, delta = F(1, 2), F(1), F(0)
    assert all(r > 0 for r in rho) and sum(rho) == F(1, 2)
    attention_weights = [r * (alpha if bit else 1)
                         for r, bit in zip(rho, bits)]
    numerator = eta + sum(a * delta * bit
                          for a, bit in zip(attention_weights, bits))
    denominator = gamma + sum(attention_weights)
    assert denominator > 0
    value = numerator / denominator
    assert value == F(1, 1 + sum(w * bit for w, bit in zip(weights, bits)))
    return value


def run():
    tables, table_values, atom_values, cases = 0, 0, 0, []
    for H, k in [(2, 2), (2, 3), (3, 2), (3, 3), (4, 2), (4, 3)]:
        d = (2 * H - 1).bit_length()
        addresses = range(1 << d)
        selector_vectors = list(product((0, 1), repeat=k))
        all_perms = list(permutations(range(H)))
        signatures, baseline = set(), None
        for ps in product(all_perms, repeat=k - 1):
            values = tuple(score(H, ps, xs, t)
                           for xs in selector_vectors for t in addresses)
            sliced = tuple(score(H, ps, xs, t)
                           for xs in selector_vectors if sum(xs) <= 1
                           for t in addresses)
            if baseline is None:
                baseline = sliced
            assert sliced == baseline
            assert values not in signatures
            signatures.add(values)
            tables += 1
            table_values += len(values)
            # Full literal atom identity on all cube inputs for each family.
            for xs in selector_vectors:
                for t in addresses:
                    bits = xs + tuple((t >> j) & 1 for j in range(d))
                    total = F(0)
                    for h in range(H):
                        weights = [h + 1] + [H * (p[h] + 1) for p in ps]
                        weights += [1 << j for j in range(d)]
                        total += atom_reciprocal(weights, bits)
                        atom_values += 1
                    assert total == score(H, ps, xs, t)
        assert len(signatures) == factorial(H) ** (k - 1)
        cases.append(dict(H=H, selectors=k, address_bits=d,
                          distinct_tables=len(signatures)))
    return dict(status="PASS", scope="finite exact diagnostics only",
                tables=tables, table_values=table_values,
                literal_atom_values=atom_values, cases=cases,
                verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__ == '__main__':
    result = run()
    output = Path(__file__).with_name('permutation-pole-rational-audit.json')
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
