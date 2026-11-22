"""Independent exact checks of the uniform root brackets and budgets.

The general theorem is a written proof. These finite checks audit constants
and both parities, not hyperbolicity for all real directions by sampling.
"""
from fractions import Fraction as Q
from math import prod
from pathlib import Path
import json


def main():
    endpoints=0
    budgets=0
    for n in range(2,65):
        m=n//2
        roots=[Q(j,n) for j in range(1,m+1)] + [-Q(j,n) for j in range(1,m+1)]
        if n%2:
            roots.append(Q(0))
        roots.sort()
        assert len(roots)==n and len(set(roots))==n
        assert all(b-a>=Q(1,n) for a,b in zip(roots,roots[1:]))
        delta=Q(1,4*n)
        eps=Q(1,2*(16*n)**n)
        assert eps*4**n==delta**n/2
        assert eps*3**n <= Q(3,4)**m/2
        budgets+=2
        for rho in roots:
            values=[]
            for side in (-1,1):
                t=rho+side*delta
                assert abs(t)<1
                value=prod(t-r for r in roots)
                assert abs(value)>=delta**n
                assert abs(value)>eps*4**n
                values.append(value)
                endpoints+=1
            assert prod(values)<0
    report=dict(status='PASS',dimensions=list(range(2,65)),exact_endpoint_checks=endpoints,
                exact_budget_checks=budgets,main_target_proved=False,
                scope='finite exact audit of root brackets and constants; no sampled-direction proof claimed')
    (Path(__file__).parent/'hyperbolic-tangent-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__=='__main__':
    main()
