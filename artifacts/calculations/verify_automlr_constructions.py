#!/usr/bin/env python3
"""Supplemental exact checks for the imported automlr constructions.

The canonical Lean results independently check the universal bound and the
small addressing certificates. These tests also exercise the general address
perturbation and the finite six-target cover optimality calculation.
"""

from fractions import Fraction as F
from functools import reduce
from itertools import combinations, product
from math import prod
from random import Random


def solve_square(rows, right_hand_side):
    """Solve a nonsingular square rational system exactly."""
    size = len(rows)
    augmented = [
        [F(value) for value in row] + [F(right_hand_side[i])]
        for i, row in enumerate(rows)
    ]
    for col in range(size):
        pivot = next((i for i in range(col, size) if augmented[i][col]), None)
        assert pivot is not None
        augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
        scale = augmented[col][col]
        augmented[col] = [value / scale for value in augmented[col]]
        for i in range(size):
            if i != col and augmented[i][col]:
                scale = augmented[i][col]
                augmented[i] = [
                    left - scale * right
                    for left, right in zip(augmented[i], augmented[col])
                ]
    return [augmented[i][-1] for i in range(size)]


def test_multicoset_syndrome_cover():
    cases = [
        (
            6,
            (17, 18, 20, 23, 26, 31, 34, 39, 56, 58, 61, 63),
            {0, 6, 10, 20, 22, 48, 49},
        ),
        (
            6,
            (6, 11, 20, 25, 33, 34, 35, 43, 46, 47, 52, 53, 62, 63),
            {0, 4, 7, 8, 43, 57},
        ),
        (
            7,
            (0, 3, 4, 14, 20, 52, 66, 89, 95, 96, 110, 115, 126),
            {0, 1, 13, 40, 69, 78, 83, 97, 104, 112, 120, 125},
        ),
    ]
    for syndrome_bits, columns, targets in cases:
        syndrome_count = 1 << syndrome_bits
        assert {
            target ^ column for target in targets for column in columns
        } == set(range(syndrome_count))
        basis = [0] * syndrome_bits
        rank = 0
        for column in columns:
            value = column
            while value:
                pivot = value.bit_length() - 1
                if basis[pivot]:
                    value ^= basis[pivot]
                else:
                    basis[pivot] = value
                    rank += 1
                    break
        assert rank == syndrome_bits

        def syndrome(word):
            out = 0
            for i, column in enumerate(columns):
                if (word >> i) & 1:
                    out ^= column
            return out

        centers = {
            word
            for word in range(1 << len(columns))
            if syndrome(word) in targets
        }
        assert len(centers) == len(targets) * (
            1 << (len(columns) - syndrome_bits)
        )
        for word in range(1 << len(columns)):
            assert any(
                (word ^ (1 << i)) in centers for i in range(len(columns))
            )

        # Algebraic verification of Cartesian lifts through three extra bits.
        for extra_bits in range(4):
            lifted_columns = {
                (column, tail)
                for column in columns
                for tail in range(1 << extra_bits)
            }
            lifted_targets = {(target, 0) for target in targets}
            assert {
                (target ^ column, target_tail ^ column_tail)
                for target, target_tail in lifted_targets
                for column, column_tail in lifted_columns
            } == {
                (head, tail)
                for head in range(syndrome_count)
                for tail in range(1 << extra_bits)
            }

    def maximum_translate_union(points, rank, translate_count):
        group_size = 1 << rank
        base_mask = sum(1 << point for point in points)
        translated = []
        for shift in range(group_size):
            translated.append(
                sum(
                    1 << (point ^ shift)
                    for point in range(group_size)
                    if (base_mask >> point) & 1
                )
            )
        return max(
            reduce(
                int.__or__,
                (translated[shift] for shift in shifts),
                0,
            ).bit_count()
            for shifts in combinations(range(group_size), translate_count)
        )

    # The five GL-types of a six-point set containing zero.  These exact
    # maxima prove that six target cosets in F_2^6 need at least 14 columns.
    assert maximum_translate_union((0, 1, 2, 4, 8, 16), 5, 6) == 30
    assert maximum_translate_union((0, 1, 2, 4, 8, 3), 4, 3) == 14
    assert maximum_translate_union((0, 1, 2, 4, 8, 7), 4, 3) == 14
    assert maximum_translate_union((0, 1, 2, 4, 8, 15), 4, 3) == 13
    assert maximum_translate_union((0, 1, 2, 3, 4, 5), 3, 1) == 6
    assert maximum_translate_union((0, 1, 2, 3, 4, 5), 3, 2) == 8

    # Exact integer audit of the three lifted intervals and their strict
    # 3/2 ratio; checking the right endpoint suffices because n/2^k is
    # increasing within each interval.
    for k in range(3, 33):
        start = 1 << k
        twelve_start = 12 << (k - 3)
        thirteen_start = 13 << (k - 3)
        end = 1 << (k + 1)
        assert start < twelve_start < thirteen_start < end
        assert twelve_start == 3 << (k - 1)
        assert k + 3 <= twelve_start and k + 4 <= thirteen_start
        assert 2 * (twelve_start - 1) < 3 * (1 << k)
        assert 14 * (thirteen_start - 1) < 3 * (1 << (k + 3))
        assert 24 * (end - 1) < 3 * (1 << (k + 4))


def test_address_two_point_cauchy_relation():
    for r in range(2, 6):
        address_count = 1 << r
        half = address_count // 2
        head_count = address_count - 1

        # P has every address node except the two even nodes 0 and m/2 as a
        # root.  Its residues beta_h at the negative Cauchy poles alternate.
        def polynomial(z):
            out = F(-1)
            for node in range(address_count):
                if node not in (0, half):
                    out *= z - node
            return out

        beta = []
        for h in range(1, address_count):
            derivative = 1
            for pole in range(1, address_count):
                if pole != h:
                    derivative *= -h + pole
            beta.append(polynomial(-h) / derivative)
        assert [1 if value > 0 else -1 for value in beta] == [
            (-1) ** h for h in range(1, address_count)
        ]

        # The rational function P/Q is supported only at those two even
        # nodes, so multiplying it by the low address bit cancels identically.
        for z in range(address_count):
            value = sum(beta[h - 1] / F(z + h) for h in range(1, address_count))
            assert value == F(polynomial(z), prod(range(z + 1, z + address_count)))
            assert (z & 1) * value == 0

        normal = []
        for z in range(address_count):
            q_value = prod(range(z + 1, z + address_count))
            derivative = 1
            for node in range(address_count):
                if node != z:
                    derivative *= z - node
            normal.append(F(q_value, derivative))
        gamma = [
            -beta[h - 1]
            * sum(
                normal[z] / F((z + h) ** 2)
                for z in range(1, address_count, 2)
            )
            for h in range(1, address_count)
        ]
        assert min(gamma) < 0 < max(gamma)


def test_address_uniform_perturbation_construction():
    """Exercise every algebraic layer of the uniform (2^r-1)-head proof."""
    for r in range(2, 4):
        address_count = 1 << r
        half = address_count // 2
        head_count = address_count - 1

        def polynomial(z):
            out = F(-1)
            for node in range(address_count):
                if node not in (0, half):
                    out *= z - node
            return out

        beta = []
        for h in range(1, address_count):
            derivative = prod(
                -h + pole
                for pole in range(1, address_count)
                if pole != h
            )
            beta.append(F(polynomial(-h), derivative))

        reciprocal = [
            [F(1, z + h) for h in range(1, address_count)]
            for z in range(address_count)
        ]
        normal = []
        for z in range(address_count):
            q_value = prod(range(z + 1, z + address_count))
            v_derivative = prod(
                z - node for node in range(address_count) if node != z
            )
            normal.append(F(q_value, v_derivative))

        generators = [
            [
                -beta[h - 1] * (z & 1) / F((z + h) ** 2)
                for z in range(address_count)
            ]
            for h in range(1, address_count)
        ]
        gamma = [
            sum(normal[z] * generators[h][z] for z in range(address_count))
            for h in range(head_count)
        ]
        assert min(gamma) < 0 < max(gamma)

        denominator_slopes = [[F(0)] * address_count for _ in range(head_count)]
        value_slopes = [[F(0)] * address_count for _ in range(head_count)]
        square_reciprocal = reciprocal[:head_count]
        for b in range(address_count):
            positive = [F(1)] * head_count
            discrepancy = normal[b] - sum(gamma)
            if discrepancy:
                chosen = next(
                    h
                    for h, value in enumerate(gamma)
                    if value * discrepancy > 0
                )
                positive[chosen] += discrepancy / gamma[chosen]
            assert all(value > 0 for value in positive)
            assert sum(g * q for g, q in zip(gamma, positive)) == normal[b]

            target = [
                F(z == b)
                - sum(positive[h] * generators[h][z] for h in range(head_count))
                for z in range(address_count)
            ]
            assert sum(c * value for c, value in zip(normal, target)) == 0
            values = solve_square(square_reciprocal, target[:head_count])
            assert all(
                sum(reciprocal[z][h] * values[h] for h in range(head_count))
                == target[z]
                for z in range(address_count)
            )
            for h in range(head_count):
                denominator_slopes[h][b] = positive[h]
                value_slopes[h][b] = values[h]

        # The finite epsilon representation is checked on every input.  The
        # loop only chooses a concrete witness; uniform convergence is proved
        # symbolically by the identities above.
        epsilon = F(1, 10)
        cube = product([0, 1], repeat=address_count)
        data_vectors = list(cube)
        while True:
            valid = True
            for z in range(address_count):
                for data in data_vectors:
                    score = F(-1, 2)
                    for h in range(1, address_count):
                        denominator = F(z + h) + epsilon * sum(
                            denominator_slopes[h - 1][b] * data[b]
                            for b in range(address_count)
                        )
                        numerator = beta[h - 1] * (z & 1) / epsilon + sum(
                            value_slopes[h - 1][b] * data[b]
                            for b in range(address_count)
                        )
                        score += numerator / denominator
                    if (1 if data[z] else -1) * score <= 0:
                        valid = False
                        break
                if not valid:
                    break
            if valid:
                break
            epsilon /= 10
            assert epsilon > F(1, 10**40)

        assert all(value > 0 for row in denominator_slopes for value in row)


def main():
    test_multicoset_syndrome_cover()
    test_address_two_point_cauchy_relation()
    test_address_uniform_perturbation_construction()
    print("syndrome covers, Cartesian lifts and finite six-target optimality: exact")
    print("two-point Cauchy identities through five address bits: exact")
    print("general addressing perturbation through three address bits: exact")


if __name__ == "__main__":
    main()
