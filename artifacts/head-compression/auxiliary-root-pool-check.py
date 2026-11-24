"""Exact positive common pools using unqueried adjacent pole pairs."""
from fractions import Fraction as Q
from itertools import product
from flint import fmpq, fmpq_mat


def fq(x): return fmpq(x.numerator, x.denominator)
def qf(x): return Q(int(x.numerator), int(x.denominator))
def matrix(a): return fmpq_mat([[fq(x) for x in row] for row in a])


def solve_setup(q, k):
    size = (q+2)//2
    m = q+k*size
    p = [Q(j+1, 100*m) for j in range(2*m)]
    t = [Q(1)+Q(j+1,q+1) for j in range(q)]
    cauchy = [[1/(x-y) for y in p] for x in t]
    # Columns of V are independent sign words; V_0=all+ and the rest flip
    # one of the first K-1 coordinates.
    v = [[Q(-1 if col and row == col-1 else 1) for col in range(k)]
         for row in range(k)]
    inverse_v = matrix(v).inv()
    groups = []
    for g in range(k):
        cols = list(range(2*(q+g*size), 2*(q+(g+1)*size)))
        a = [[cauchy[i][h]*(1 if j%2==0 else -1)
              for j,h in enumerate(cols)] for i in range(q)]
        first_inv = matrix([row[:q] for row in a]).inv()
        # Alternating Cauchy minors yield a strictly positive kernel.
        z = [qf(matrix([[row[j] for j in range(q+1) if j!=omit]
                         for row in a]).det())*((-1)**omit)
             for omit in range(q+1)]
        if z[0] < 0: z = [-x for x in z]
        assert all(x>0 for x in z)
        assert all(sum(a[i][j]*z[j] for j in range(q+1)) == 0 for i in range(q))
        groups.append((cols,a,first_inv,z))
    return m,p,t,cauchy,v,inverse_v,groups


def check(q,k):
    m,p,t,cauchy,v,inverse_v,groups = solve_setup(q,k)
    count = 0
    for flat in product((-1,1), repeat=k*q):
        words = [flat[a*q:(a+1)*q] for a in range(k)]
        # Selected pairs get residue one and the required, fixed routing bits.
        residues = [Q(1)]*(2*m)
        residual = [[Q(words[a][j])-sum(words[a][s]*(cauchy[j][2*s]-cauchy[j][2*s+1])
                                          for s in range(q))
                     for j in range(q)] for a in range(k)]
        targets = inverse_v*matrix(residual)
        for g,(cols,a,first_inv,z) in enumerate(groups):
            # Leave all but the first q coordinates equal to one initially.
            rhs = [qf(targets[g,i])-sum(a[i][h] for h in range(q,len(cols))) for i in range(q)]
            first = first_inv*matrix([[x] for x in rhs])
            c = [qf(first[j,0]) for j in range(q)]+[Q(1)]*(len(cols)-q)
            shift = 1+max([Q(0)]+[-c[j]/z[j] for j in range(q+1)])
            for j in range(q+1): c[j] += shift*z[j]
            assert all(x>0 for x in c)
            assert all(sum(a[i][j]*c[j] for j in range(len(cols))) == qf(targets[g,i])
                       for i in range(q))
            for h,x in zip(cols,c): residues[h] = x
        for a in range(k):
            routing = list(words[a])+[int(v[a][g]) for g in range(k) for _ in range((q+2)//2)]
            for j in range(q):
                score = sum(routing[s]*(residues[2*s]*cauchy[j][2*s]
                                         -residues[2*s+1]*cauchy[j][2*s+1])
                            for s in range(m))
                assert score == words[a][j]
        count += 1
    print(f'q={q}, K={k}, M={m}: {count} positive shared-pool certificates', flush=True)
    return count


if __name__ == '__main__':
    total = sum(check(q,k) for q in range(1,4) for k in range(1,4))
    total += sum(check(q,2) for q in (4,5))
    print(f'All {total} exact root-only certificates passed; descendants are not constrained.')
