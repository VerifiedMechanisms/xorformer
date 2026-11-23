#!/usr/bin/env python3
"""Exact finite replays of the general denominator-parameter identities."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import random

BASE=Path(__file__).parent

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def mv(a,v): return [dot(row,v) for row in a]
def qform(b,v): return sum(t*x*x for t,x in zip(b,v))+dot(b,v)**2

def check(n,b,a,mu):
    X=[[(v>>i)&1 for i in range(n)] for v in range(2**n)]
    D=[1+dot(b,x) for x in X]
    T=[(a[0]+dot(a[1:],x))/d for x,d in zip(X,D)]
    assert any(T) and min(D)>0
    A=[[b[i]*b[j]+(b[i] if i==j else 0) for j in range(n)] for i in range(n)]
    dT=[[-t*F(xi)/d for xi in x] for x,d,t in zip(X,D,T)]
    ddT=[[[2*t*F(x[i]*x[j])/d**2 for j in range(n)] for i in range(n)] for x,d,t in zip(X,D,T)]
    for dt,ddt in zip(dT,ddT):
        assert sum(A[i][j]*ddt[i][j] for i in range(n) for j in range(n))+2*dot(b,dt)==0
    G=dot(T,T)
    dG=[2*sum(T[x]*dT[x][i] for x in range(len(X))) for i in range(n)]
    ddG=[[2*sum(dT[x][i]*dT[x][j]+T[x]*ddT[x][i][j] for x in range(len(X))) for j in range(n)] for i in range(n)]
    p=[t*t/G for t in T]
    v=[[F(xi)/d for xi in x] for x,d in zip(X,D)]
    m=[sum(p[x]*v[x][i] for x in range(len(X))) for i in range(n)]
    assert m==[-z/(2*G) for z in dG]
    for vx in v: assert qform(b,vx)==dot(b,vx)
    V=dot(b,m)-qform(b,m)
    variance=sum(px*qform(b,[vi-mi for vi,mi in zip(vx,m)]) for px,vx in zip(p,v))
    assert V==variance
    E=sum(qform(b,dt) for dt in dT)
    assert V==E/G-qform(b,dG)/(4*G**2)
    B=sum(b);c=1/(2*(1+B));radius=B/(4*(1+B))
    assert V==radius-qform(b,[z-c for z in m])
    assert 0<=V<=radius<F(1,4)
    R=dot(mu,T)
    dR=[sum(mu[x]*dT[x][i] for x in range(len(X))) for i in range(n)]
    ddR=[[sum(mu[x]*ddT[x][i][j] for x in range(len(X))) for j in range(n)] for i in range(n)]
    # These are the first and second derivatives of R/sqrt(G), multiplied
    # by sqrt(G). Thus every calculation below stays in rational arithmetic.
    dh=[dR[i]-R*dG[i]/(2*G) for i in range(n)]
    ddh=[[ddR[i][j]-(dR[i]*dG[j]+dR[j]*dG[i])/(2*G)-R*ddG[i][j]/(2*G)+3*R*dG[i]*dG[j]/(4*G**2) for j in range(n)] for i in range(n)]
    Am=mv(A,m);drift=[2*(bi-ami) for bi,ami in zip(b,Am)]
    assert sum(A[i][j]*ddh[i][j] for i in range(n) for j in range(n))+dot(drift,dh)+V*R==0
    return dict(n=n,b=[str(z) for z in b],a=[str(z) for z in a],mu=mu,
        potential=str(V),radius_squared=str(radius),zero_table_entries=T.count(F(0)))

def main():
    rng=random.Random(202611231635)
    rows=[]
    for n in range(1,8):
        for case in range(8):
            if case<4: b=[F(rng.randint(1,12),rng.randint(1,9)) for _ in range(n)]
            else: b=[F(10)**rng.randint(-6,6) for _ in range(n)]
            a=[F(rng.randint(-5,5)) for _ in range(n+1)]
            if not any(a): a[0]=F(1)
            mu=[rng.randint(-10,10) for _ in range(2**n)]
            rows.append(check(n,b,a,mu))
    report=dict(status='PASS',cases=len(rows),cube_entries=sum(2**x['n'] for x in rows),
        arithmetic='fractions.Fraction only',checks=['unnormalized elliptic equation','Boolean sphere identity','normalized derivative and covariance formulas','exact square completion','nonnegative potential below one quarter','normalized height elliptic equation'],
        cases_data=rows,verifier_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        scope='finite replays supplement the general written and algebraic Lean proofs',main_target_proved=False)
    (BASE/'head-elliptic-rational-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='cases_data'},indent=2))

if __name__=='__main__': main()
