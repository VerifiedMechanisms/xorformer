#!/usr/bin/env python3
"""Exact finite diagnostics for the reciprocal mean-value and amplitude identities."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import random

ROOT=Path(__file__).resolve().parent
RNG=random.Random(1481183)


def moment(w, mask):
    ans=Q(0)
    t=mask
    while True:
        ans+=Q((-1)**t.bit_count(), 1+sum(w[i] for i in range(len(w)) if (t>>i)&1))
        if t==0:
            return ans
        t=(t-1)&mask


def main():
    cases=vertices=mean_checks=sharpness_checks=0
    for n in range(1,9):
        full=(1<<n)-1
        for _ in range(35):
            w=[Q(RNG.randrange(15),RNG.randrange(1,8)) for _ in range(n)]
            a=[Q(RNG.randrange(-20,21),RNG.randrange(1,8)) for _ in range(n)]
            a0=Q(RNG.randrange(-20,21),RNG.randrange(1,8))
            table=[(a0+sum(a[i] for i in range(n) if (x>>i)&1))/(1+sum(w[i] for i in range(n) if (x>>i)&1)) for x in range(1<<n)]
            K=moment(w,full)
            assert 0<=K<1
            d=[moment(w,full^(1<<i))-K for i in range(n)]
            assert sum(wi*di for wi,di in zip(w,d))==K
            z=[di/(1-K) for di in d]
            assert all(0<=zi<=1 for zi in z)
            L=sum(((-1)**x.bit_count())*f for x,f in enumerate(table))
            inside=(a0+sum(ai*zi for ai,zi in zip(a,z)))/(1+sum(wi*zi for wi,zi in zip(w,z)))
            assert L==a0-inside
            M=max(abs(f) for f in table)
            assert abs(L)<=2*M
            # All-coordinate complementation preserves absolute correlation.
            flipped=sum(((-1)**x.bit_count())*table[full^x] for x in range(1<<n))
            assert flipped==((-1)**n)*L
            cases+=1
            vertices+=1<<n
            mean_checks+=1
        for t in [Q(1),Q(100),Q(10**6)]:
            table=[1-Q(2,1+t*x.bit_count()) for x in range(1<<n)]
            L=sum(((-1)**x.bit_count())*f for x,f in enumerate(table))
            assert max(abs(f) for f in table)==1
            assert abs(L+2)<=Q(2*((1<<n)-1),1+t)
            # A literal admissible atom realizes this sharpness family.
            rho=Q(1,2*n)
            alpha=1+2*n*t
            for x in range(1<<n):
                total=sum(rho*(alpha if (x>>i)&1 else 1) for i in range(n))
                actual=(Q(-3,2)+total)/(Q(1,2)+total)
                assert actual==table[x]
            sharpness_checks+=1
    report={'status':'PASS','rational_tables':cases,'cube_vertices':vertices,'exact_mean_value_checks':mean_checks,'sharpness_families_and_atom_checks':sharpness_checks,'arithmetic':'exact fractions only','scope':'finite independent diagnostic; universal theorem is kernel checked separately','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'main_target_proved':False}
    (ROOT/'head-parity-rational-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
