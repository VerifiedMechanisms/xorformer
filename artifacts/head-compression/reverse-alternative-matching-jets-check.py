"""Exact checks for axis-zero matching jets. No universality search."""

from fractions import Fraction as F
from itertools import product
import sympy as s

eta, R, t, xi, u, v, c = s.symbols("eta R t xi u v c")
bracket = u/(t-xi) - (u+c)/(t-xi-eta*R)
bracket -= v/(t-xi-2*eta*R)
bracket += (v+c)/(t-xi-3*eta*R)
assert s.cancel(bracket.subs(eta, 0)) == 0
assert s.cancel(s.diff(bracket, eta).subs(eta, 0)
                - R*(v-u+2*c)/(t-xi)**2) == 0

def matchings(k):
    vertices = list(product((0, 1), repeat=k))
    even = [h for h in vertices if sum(h) % 2 == 0]
    odd = [h for h in vertices if sum(h) % 2 == 1]
    neighbors = {h: [v for v in odd if sum(x != y for x, y in zip(h, v)) == 1]
                 for h in even}
    def extend(i, used, current):
        if i == len(even):
            yield dict(current)
            return
        h = even[i]
        for v in neighbors[h]:
            if v not in used:
                current[h] = v
                yield from extend(i+1, used | {v}, current)
                del current[h]
    return vertices, even, list(extend(0, set(), {}))

checks = 0
for k, expected_count in ((2, 2), (3, 9)):
    vertices, even, states = matchings(k)
    assert len(states) == expected_count
    r, column_count = 2, 2
    row_slopes = [F(1, 5), F(2, 5)]
    cs = [F(2), F(-3)]
    profiles = [{h: F((i+2)*sum((j+1)*bit for j, bit in enumerate(h))-3)
                 for h in vertices} for i in range(r)]
    selected = [states[0], states[-1]]
    eta_value = F(1, 100)
    xis = {g: F(j+1) for j, g in enumerate(even)}
    weights = {g: F(j+2) for j, g in enumerate(even)}
    L = F(10*len(even))
    C = F(r) + column_count*L + 1
    poles = []
    for matching in selected:
        table = {}
        for g, neighbor in matching.items():
            for position, slot in enumerate(((g, 0), (g, 1), (neighbor, 0), (neighbor, 1))):
                table[slot] = xis[g] + eta_value*weights[g]*position
        assert all(0 < value < L for value in table.values())
        poles.append(table)
    slots = [(h, a) for h in vertices for a in (0, 1)]
    def score(z, w):
        answer = F(0)
        for h, a in slots:
            denominator = C-sum(row_slopes[i]*z[i] for i in range(r))
            denominator -= sum(poles[j][h, a]*w[j] for j in range(column_count))
            assert denominator > 0
            sign = (-1)**(sum(h)+a)
            numerator = sum((profiles[i][h]+a*cs[i])*z[i] for i in range(r))
            answer += sign*numerator/(eta_value*denominator)
        return answer
    for z in product((0, 1), repeat=r):
        for w in product((0, 1), repeat=column_count):
            value = score(z, w)
            if not any(z) or not any(w):
                assert value == 0
            checks += 1
print(f"PASS: symbolic edge jet, matching counts2 and9, {checks} exact full-cube checks.")
