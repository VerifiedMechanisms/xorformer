"""Generate rational pure3 candidates and query all-admissible vanilla3 NRA.
Numerical failure is only a screening heuristic. Only an exact solver's UNSAT
answer on all four orientation counts could supply a lower bound.
Run all solver/search campaigns with heavy.
"""
import argparse
from fractions import Fraction as Q
import itertools
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import linprog
from search_vandermonde_perturb import fit_vanilla,vertices


def candidate(n,rng,balanced=False):
    ts=([Q(1,50),Q(1,20),Q(2,25)] if balanced else [Q(1,40),Q(7,100),Q(13,100)]);c=1/(ts[0]*ts[1]*ts[2]);atoms=[]
    for h,t in enumerate(ts):
        pole=-1/t;eta=(pole**3-4*pole)
        for j,tj in enumerate(ts):
            if j!=h:eta/=1+tj*pole
        beta=[int(1000*t)]*3+[int(v) for v in rng.integers(-100,101,n-3)]
        if balanced:beta[-1]=-sum(beta[:-1])
        center=1000+sum(beta[3:]);gamma=center-sum(abs(v) for v in beta)-n
        if gamma<=0:return candidate(n,rng,balanced)
        aa=[1+max(-2*v,0) for v in beta];bb=[1+max(2*v,0) for v in beta]
        atoms.append({'a':aa,'b':bb,'gamma':gamma,'eta':[1000*eta.numerator,eta.denominator],'v0':0,'v1':0})
    scores=[c+sum(Q(*p['eta'])/(p['gamma']+sum(p['b'][i] if mask>>i&1 else p['a'][i] for i in range(n))) for p in atoms) for mask in range(1<<n)]
    if any(q==0 for q in scores):
        eps=min(abs(q) for q in scores if q)/2;c+=eps;scores=[q+eps for q in scores]
    y=np.array([1 if q>0 else -1 for q in scores]);truth=sum(int(t>0)<<i for i,t in enumerate(y))
    assert all(y[m]==(1 if (2*((m>>0)&1)-1)*(2*((m>>1)&1)-1)*(2*((m>>2)&1)-1)>0 else -1) for m in range(8))
    margin=min(abs(q) for q in scores)
    return y,{'n':n,'atoms':atoms,'constant':[c.numerator,c.denominator],'truth_table':hex(truth),'minimum_margin':[margin.numerator,margin.denominator],'parity_three_restriction':'coordinates0,1,2 free; all other bits zero'}


def solve_all_orientations(rec,timeout):
    import z3
    n=rec['n'];truth=int(rec['truth_table'],16);rs=[]
    for negative in range(4):
        solver=z3.SolverFor('QF_NRA');solver.set(timeout=timeout)
        b=[[z3.Real(f'b_{h}_{i}') for i in range(n)] for h in range(3)]
        a=[[z3.Real(f'a_{h}_{i}') for i in range(n+1)] for h in range(3)]
        for row in b:solver.add(*(v>0 for v in row),sum(row)<1)
        for mask in range(1<<n):
            z=[2*((mask>>i)&1)-1 for i in range(n)]
            d=[1+(-1 if h<negative else 1)*sum(b[h][i]*z[i] for i in range(n)) for h in range(3)]
            nums=[a[h][0]+sum(a[h][i+1]*z[i] for i in range(n)) for h in range(3)]
            p=sum(nums[h]*d[(h+1)%3]*d[(h+2)%3] for h in range(3))
            solver.add((1 if truth>>mask&1 else -1)*p>=1)
        start=time.time();answer=solver.check();r={'negative_heads':negative,'answer':str(answer),'seconds':time.time()-start}
        if answer==z3.unknown:r['reason']=solver.reason_unknown()
        rs.append(r);print('NRA',r,flush=True)
        if answer==z3.sat:break
    return rs


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=6);ap.add_argument('--samples',type=int,default=300);ap.add_argument('--restarts',type=int,default=8);ap.add_argument('--seed',type=int,default=323671);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--balanced',action='store_true');ap.add_argument('--nra-timeout',type=int,default=0);a=ap.parse_args();rng=np.random.default_rng(a.seed);z=vertices(a.n)
    f2=np.column_stack([np.ones(len(z)),z]+[z[:,i]*z[:,j] for i in range(a.n) for j in range(i)])
    kept=0
    for j in range(a.samples):
        y,rec=candidate(a.n,rng,a.balanced)
        kept+=1;fit=fit_vanilla(z,y,a.restarts,rng);rec.update({'sample':j,'seed':a.seed,'quadratic_screen':'explicit parity-three restriction','vanilla_search':fit})
        if fit['status']=='unresolved' and a.nra_timeout:rec['NRA']=solve_all_orientations(rec,a.nra_timeout)
        with a.out.open('a') as out:out.write(json.dumps(rec)+'\n')
        print('candidate',j,'kept',kept,fit['status'],fit['loss'],flush=True)

if __name__=='__main__':main()
