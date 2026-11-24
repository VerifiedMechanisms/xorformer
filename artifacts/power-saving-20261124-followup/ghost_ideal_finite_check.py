"""Exact finite checks for the written ghost-ideal analysis.

Ranks are computed over the prime field F_1000003; they do not prove the
all-dimension ideal theorem, whose proof is in the accompanying Markdown.
"""
from collections import defaultdict
from itertools import product
import sympy as sp

PRIME = 1000003

def compositions(d, n):
    if n == 1:
        yield (d,)
    else:
        for a in range(d + 1):
            for tail in compositions(d - a, n - 1):
                yield (a,) + tail

def rank_mod(columns, nrows):
    pivots = {}
    for column in columns:
        v = [int(a) % PRIME for a in column]
        for k in sorted(pivots):
            if v[k]:
                c = v[k]
                v = [(a-c*b) % PRIME for a, b in zip(v, pivots[k])]
        k = next((i for i, a in enumerate(v) if a), None)
        if k is not None:
            inv = pow(v[k], -1, PRIME)
            pivots[k] = [(a*inv) % PRIME for a in v]
    return len(pivots)

def exp_term(nvar, inds):
    out = [0] * nvar
    for i in inds:
        out[i] += 1
    return tuple(out)

def generator_terms(n, r):
    out = []
    for i, j in product(range(n), repeat=2):
        for q, s in product(range(r), repeat=2):
            u = exp_term(n*r, [i*r+q, j*r+s])
            v = exp_term(n*r, [i*r+s, j*r+q])
            if u != v:
                out.append((2, {u: 1, v: -1}))
            for t in range(r):
                u = exp_term(n*r, [i*r+q, j*r+s, i*r+t])
                v = exp_term(n*r, [i*r+q, j*r+s, j*r+t])
                if u != v:
                    out.append((3, {u: 1, v: -1}))
    return out

def check_degree(n, r, d):
    mons = list(compositions(d, n*r))
    idx = {a:i for i,a in enumerate(mons)}
    generators = []
    for degree, terms in generator_terms(n, r):
        if degree > d:
            continue
        for multiplier in compositions(d-degree, n*r):
            v = [0]*len(mons)
            for monomial, coeff in terms.items():
                shifted = tuple(a+b for a,b in zip(monomial,multiplier))
                v[idx[shifted]] += coeff
            generators.append(v)
    rank_generators = rank_mod(generators, len(mons))
    # Columns of the evaluation map, with rows indexed by (Boolean T,beta).
    betas = list(compositions(d, r))
    row_idx = {(T,b):i for i,(T,b) in enumerate(product(range(2**n),betas))}
    evaluations = []
    for monomial in mons:
        support = sum(1 << i for i in range(n) if any(monomial[i*r+q] for q in range(r)))
        beta = tuple(sum(monomial[i*r+q] for i in range(n)) for q in range(r))
        v = [0] * len(row_idx)
        for T in range(2**n):
            if support & T == support:
                v[row_idx[T,beta]] = 1
        evaluations.append(v)
    rank_eval = rank_mod(evaluations, len(row_idx))
    expected = sum(sp.binomial(n,k) for k in range(1,min(n,d)+1))*sp.binomial(r+d-1,d)
    assert rank_eval == expected
    assert rank_generators + rank_eval == len(mons)
    print(f'n={n} r={r} degree={d}: monomials={len(mons)} ideal_rank={rank_generators} eval_rank={rank_eval}')

for n,r,maxd in [(2,1,8),(3,1,8),(2,2,5),(3,2,4)]:
    for d in range(1,maxd+1):
        check_degree(n,r,d)

x,y = sp.symbols('x y')
g = lambda u,v: (u-1)*(v-1)*(u-v)
for M in range(1,13):
    Q = sp.Poly(sp.expand(sum(x**a for a in range(M))*sum(y**b for b in range(M))*sum(x**(M-1-c)*y**c for c in range(M))),x,y)
    assert sp.expand(g(x**M,y**M)-g(x,y)*Q.as_expr()) == 0
    assert len(Q.terms()) == 3*M*M-3*M+1
    assert Q.eval({x:1,y:1}) == M**3
    assert all(c > 0 for c in Q.coeffs())
    print(f'scaled six-term ghost M={M}: unit_quotient_support={len(Q.terms())} coefficient_mass={M**3}')

a,b,c = 1,3,7
R = sp.expand((x**a-1)*(y**c-1)*(x**b-y**b))
minor = lambda u,v: (x**u-1)*(y**v-1)-(x**v-1)*(y**u-1)
assert sp.expand(R-minor(b+c,a)+x**b*minor(c,a)+minor(b,a)) == 0
terms = sp.Poly(R,x,y).terms()
assert len(terms)==8
A=[]
for key in (lambda p:p[0],lambda p:p[1],lambda p:sum(p)):
    for value in sorted({key(p) for p,_ in terms}):
        A.append([int(key(p)==value) for p,_ in terms])
assert sp.Matrix(A).rank()==7
assert all(coeff != 0 for _,coeff in terms)
print('Eight-point example: projection matrix rank7, all8 nonzero, hence a circuit; exact three-hexagon identity verified.')
