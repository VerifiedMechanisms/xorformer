#!/usr/bin/env python3
"""Independent rational checks of the clipped-gap and head-table estimates.

Finite checks accompany the written universal proof; they are not a proof of it.
"""
from fractions import Fraction as Q
from itertools import combinations
import hashlib
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent
RNG = random.Random(771409)


def params(m, epsilon):
    r = 1 + epsilon / (16*m)
    threshold = 16*m/epsilon
    K, p = 0, Q(1)
    while p < threshold:
        K, p = K+1, p*r
    return r, K


def floor_log_capped(g, r, K):
    lo, hi = 0, K+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        if r**mid <= g:
            lo = mid
        else:
            hi = mid
    return lo


def quantize(w, epsilon):
    m = len(w)
    r, K = params(m, epsilon)
    order = sorted(range(m), key=lambda j: (w[j], j))
    v = [Q(0)]*m
    v[order[0]] = 1
    for a, b in zip(order, order[1:]):
        q = floor_log_capped(w[b]/w[a], r, K)
        v[b] = v[a]*r**q
    return v


def menus(m):
    return [s for k in range(1,m+1) for s in combinations(range(m),k)]


def choice(w, s):
    den = sum(w[i] for i in s)
    return [w[i]/den if i in s else Q(0) for i in range(len(w))]


def head(w, z, s):
    p = choice(w, (0,)+s)
    return p[0]*(z[0]*(1-len(s))+sum(z[i] for i in s)) + sum(p[i]*z[i] for i in s)


def main():
    choice_checks = head_checks = 0
    max_relative_error = Q(0)
    for m in range(2,7):
        epsilon = Q(1)
        r, K = params(m, epsilon)
        cases = [[Q(1)]*m, [Q(2)**(30*i) for i in range(m)]]
        for spike in range(m-1):
            gaps = [r**(K//3)]*(m-1)
            gaps[spike] = r**(K+9)
            w = [Q(1)]
            for g in gaps:
                w.append(w[-1]*g)
            cases.extend([w, list(reversed(w))])
        for _ in range(4):
            cases.append([Q(RNG.randint(1,99), RNG.randint(1,19))*Q(2)**RNG.randint(-120,120) for _ in range(m)])
        for w in cases:
            v = quantize(w, epsilon)
            for s in menus(m):
                error = sum(abs(a-b) for a,b in zip(choice(w,s),choice(v,s)))
                assert error <= epsilon/2
                max_relative_error = max(max_relative_error, error/epsilon)
                choice_checks += 1
        # Smaller dimensions suffice for the finer head net's independent checks.
        if m <= 4:
            tau = epsilon/(4*m)
            for w in cases[:4]:
                v = quantize(w,tau)
                z = [Q(RNG.randint(-100,100),100) for _ in range(m)]
                # Downward rounding on a mesh starting at -1; all values remain in [-1,1].
                zr = [-1 + ((x+1)//tau)*tau for x in z]
                for s in [()]+menus(m-1):
                    s = tuple(i+1 for i in s)
                    original = head(w,z,s)
                    direct = (z[0]*w[0]+sum((w[0]+w[i])*z[i]-z[0]*w[0] for i in s))/(w[0]+sum(w[i] for i in s))
                    assert original == direct
                    assert abs(original-head(v,zr,s)) <= epsilon
                    head_checks += 1
    report = {
        'status': 'PASS',
        'choice_menu_checks': choice_checks,
        'head_identity_and_error_checks': head_checks,
        'largest_observed_choice_error_over_epsilon_upper_decimal': float(max_relative_error),
        'arithmetic': 'exact fractions for every assertion; decimal is report only',
        'scope': 'finite diagnostic, not a substitute for the universal proof',
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'main_target_proved': False,
    }
    (ROOT/'luce-covering-rational-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__ == '__main__':
    main()
