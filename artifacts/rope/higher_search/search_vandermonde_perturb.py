"""Exploration, never a lower bound: asymmetric perturbations of a pure cubic.
Run substantial campaigns with heavy. Exact arithmetic determines every label.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import linprog, minimize


def vertices(n):
    return np.array([[2*((k>>i)&1)-1 for i in range(n)] for k in range(1<<n)],float)


def fit_vanilla(Z,y,restarts,rng):
    h=3;n=Z.shape[1]; X=np.column_stack([np.ones(len(Z)),Z]); best=1e99
    for restart in range(restarts):
        signs=np.ones(h); signs[:restart%4]=-1
        def fg(theta):
            L=theta[:h*(n+1)].reshape(h,n+1); W=np.exp(L-L.max(axis=1,keepdims=True));W/=W.sum(axis=1,keepdims=True)
            B=signs[:,None]*W[:,1:];D=1+Z@B.T
            A=theta[h*(n+1):].reshape(h,n+1);N=X@A.T
            F=np.column_stack([D[:,1]*D[:,2],D[:,0]*D[:,2],D[:,0]*D[:,1]])
            P=np.sum(N*F,axis=1);gap=np.minimum(y*P-1,0);gp=2*gap*y/len(y)
            loss=np.mean(gap*gap)+1e-10*np.sum(A*A)
            gA=(X.T@(gp[:,None]*F)).T+2e-10*A
            gD=np.column_stack([N[:,1]*D[:,2]+N[:,2]*D[:,1],N[:,0]*D[:,2]+N[:,2]*D[:,0],N[:,0]*D[:,1]+N[:,1]*D[:,0]])
            gB=(Z.T@(gp[:,None]*gD)).T
            gW=np.column_stack([np.zeros(h),signs[:,None]*gB]);gL=W*(gW-np.sum(gW*W,axis=1,keepdims=True))
            return loss,np.r_[gL.ravel(),gA.ravel()]
        theta=rng.normal(size=2*h*(n+1));theta[:h*(n+1)]*=2
        opt=minimize(fg,theta,jac=True,method='L-BFGS-B',options={'maxiter':3500,'ftol':1e-13,'gtol':1e-8})
        best=min(best,opt.fun)
        L=opt.x[:h*(n+1)].reshape(h,n+1);W=np.exp(L-L.max(axis=1,keepdims=True));W/=W.sum(axis=1,keepdims=True)
        B=signs[:,None]*W[:,1:];D=1+Z@B.T
        F=np.column_stack([X*(D[:,(i+1)%3]*D[:,(i+2)%3])[:,None] for i in range(3)])
        lp=linprog(np.zeros(3*(n+1)),A_ub=-y[:,None]*F,b_ub=-np.ones(len(y)),bounds=[(None,None)]*(3*(n+1)),method='highs')
        if lp.success and min(y*(F@lp.x))>.9:
            return {'status':'floating_fit','restarts':restart+1,'loss':float(best),'B':B.tolist(),'numerators':lp.x.reshape(3,n+1).tolist()}
    return {'status':'unresolved','restarts':restarts,'loss':float(best)}


def signs_exact(atoms,c,n):
    ys=[];m=None
    for v in range(1<<n):
        score=c
        for p in atoms:
            D=p['gamma']+sum(p['b'][i] if (v>>i)&1 else p['a'][i] for i in range(n))
            N=p['eta']+sum(p['b'][i]*p['v1'] if (v>>i)&1 else p['a'][i]*p['v0'] for i in range(n))
            score+=N/D
        if score==0:ys.append(0)
        else:ys.append(1 if score>0 else -1)
        if score and (m is None or abs(score)<m):m=abs(score)
    return ys,m


def sample(n,rng):
    # A signed circulation pencil; all three denominator directions can be mixed.
    M=np.array([[-3,1,-1],[-1,-3,1],[1,-1,-3]],dtype=int)
    adj=np.array([[-10,-4,2],[2,-10,-4],[-4,2,-10]],dtype=int)
    assert np.array_equal(M@adj,36*np.eye(3,dtype=int))
    masses=rng.integers(1,33,(3,n));numer=adj@masses
    t=16;L=2*t*int(masses.sum());atoms=[]
    for h in range(3):
        a=(36*t*masses[h]-numer[h]).tolist();b=(36*t*masses[h]+numer[h]).tolist()
        assert min(a)>0 and min(b)>0
        eta=-sum((a[i]*(-3*t+1)+b[i]*(-3*t-1))//2 for i in range(n))
        atoms.append({'a':list(map(Q,a)),'b':list(map(Q,b)),'gamma':Q(36*L-36*t*int(masses[h].sum())),'eta':Q(eta),'v0':Q(-3*t+1),'v1':Q(-3*t-1)})
    baseline,margin=signs_exact(atoms,Q(0),n)
    # Values and readout perturbations are uniformly bounded by this budget.
    eps=margin/Q(100) if margin else Q(1,1000000)
    for p in atoms:
        p['v0']+=eps*int(rng.integers(-4,5));p['v1']+=eps*int(rng.integers(-4,5));p['eta']+=eps*p['gamma']*int(rng.integers(-4,5))
    c=eps*Q(int(rng.integers(-8001,8002)),1000)
    y,newmargin=signs_exact(atoms,c,n)
    if 0 in y:return sample(n,rng)
    assert all(b==0 or a==b for a,b in zip(y,baseline))
    encode=lambda v:[v.numerator,v.denominator]
    data={'atoms':[{k:[encode(x) for x in v] if isinstance(v,list) else encode(v) for k,v in p.items()} for p in atoms], 'constant':encode(c),'truth_table':hex(sum((v>0)<<i for i,v in enumerate(y))),'baseline_zero_vertices':baseline.count(0),'minimum_absolute_score':encode(newmargin),'globally_complement_invariant':all(y[i]==y[(1<<n)-1-i] for i in range(1<<n))}
    return np.array(y,dtype=float),data


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--n',type=int,default=8);ap.add_argument('--samples',type=int,default=20);ap.add_argument('--restarts',type=int,default=8);ap.add_argument('--seed',type=int,default=49323);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();rng=np.random.default_rng(a.seed);Z=vertices(a.n)
    for j in range(a.samples):
        start=time.time();y,p=sample(a.n,rng);fit=fit_vanilla(Z,y,a.restarts,rng);r={'sample':j,'n':a.n,'pure_certificate':p,'vanilla_search':fit,'seconds':time.time()-start}
        with a.out.open('a') as f:f.write(json.dumps(r)+'\n')
        print(j,p['baseline_zero_vertices'],fit['status'],fit['loss'],round(r['seconds'],2),flush=True)
if __name__=='__main__':main()
