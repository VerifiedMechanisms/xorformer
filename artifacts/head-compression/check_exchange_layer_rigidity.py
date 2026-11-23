"""Exact finite checks for the manual equal-base exchange rigidity proof.

The checks verify formulas and ranks on finite data. The theorem for all
n >= 11 is the independent interpolation proof in the TeX note.
"""
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import random
import time
from flint import fmpq_mat


def rank(rows):
    return fmpq_mat([[str(x) for x in row] for row in rows]).rank()


def main():
    start = time.monotonic()
    rng = random.Random(23111851)
    b = 10
    ranks = []
    for n, alpha in product((11, 12, 13), (7, 10, 13)):
        for poles in product((1, 4, 9, 16), repeat=4):
            rows = []
            for k in range(2, n - 1):
                t = (alpha+b*k)**2
                rows.append([F(alpha*(n-2*k),t-poles[0]), -F(alpha*(n-2*k),t-poles[1]),
                             F(b*k,t-poles[2]), -F(b*k,t-poles[3])])
            actual = rank(rows)
            expected = 4 - int(poles[0] == poles[1]) - int(poles[2] == poles[3])
            assert actual == expected, (n, poles, actual, expected)
            ranks.append(actual)
    swaps = 0
    direct = 0
    for n, alpha in product((11, 12, 13), (7, 10, 13)):
        edges = [(i,j) for i in range(n+1) for j in range(i+1,n+1)]
        delta = {e:rng.randrange(1,min(alpha,b)) for e in edges}
        weight = {e:rng.randrange(-9,10) for e in edges}
        for _ in range(128):
            k = rng.randrange(2,n-1)
            j,l = rng.sample(range(1,n+1),2)
            rest = [i for i in range(1,n+1) if i not in (j,l)]
            S = set(rng.sample(rest,k-1))
            t = (alpha+b*k)**2
            r = {e:F(weight[e]*delta[e]**2,t-delta[e]**2) for e in edges}
            def rv(i,j): return r[tuple(sorted((i,j)))]
            def Q(X):
                return alpha*sum(rv(i,j)*int((i in X)!=(j in X))
                           for i in range(1,n+1) for j in range(i+1,n+1)) \
                       - b*k*sum(rv(0,i) for i in range(1,n+1) if i not in X)
            diff = {i:rv(i,j)-rv(i,l) for i in rest}
            expected = alpha*(sum(diff.values())-2*sum(diff[i] for i in S))+b*k*(rv(0,j)-rv(0,l))
            assert Q(S|{j})-Q(S|{l}) == expected
            swaps += 1
            X = S|{j}
            z = [1]+[int(i in X) for i in range(1,n+1)]
            B = alpha+b*k
            score = F(0)
            for (i,j) in edges:
                d=delta[i,j]
                plusB=B+d*(z[i]-z[j]); minusB=B-d*(z[i]-z[j])
                plus0=alpha+d*(int(i==0)-int(j==0))
                minus0=alpha-d*(int(i==0)-int(j==0))
                E=F(plus0,plusB)+F(minus0,minusB)-2*F(alpha,B)
                score += weight[i,j]*E
            assert score == F(2,B)*Q(X)
            direct += 1
    out={'status':'passed','dimensions':[11,12,13],'constant_coefficients':[7,10,13],'variable_coefficient':10,
         'four_pole_rank_cases':len(ranks),'rank_distribution':{str(i):ranks.count(i) for i in sorted(set(ranks))},
         'layer_swap_checks':swaps,'direct_reciprocal_checks':direct,
         'arithmetic':'Exact fractions and rational matrix ranks',
         'scope':'Finite formula and rank checks only. The all-dimension theorem is the separate manual interpolation proof.',
         'seconds':time.monotonic()-start}
    path=Path('artifacts/head-compression/diagnostics/exchange-layer-rigidity.json')
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))


if __name__ == '__main__':
    main()
