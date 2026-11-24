"""Candidate-specific quadratic sign-cone tests for pure-four projections.

Numerical LP infeasibility is not itself a certificate. A future exact dual must
be checked before claiming that every sign polynomial has an oriented cross
obstruction. This script reports diagnostics only.
"""
import argparse,itertools,json,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def load(path):
    r=json.loads(Path(path).read_text())
    mat=lambda key:np.array([[float(Fraction(v)) for v in row] for row in r[key]])
    order=[i for j in range(8) for i in [j+1,j+9]]+[0]
    S=mat('S')[order];B=mat('B')[order];U=mat('U')[order]
    return r,S,B,U,float(Fraction(r['T']))


def data(S,B,U,T,actual=True):
    # One representative from every spatial global-complement orbit.
    z=np.array([[1]+[2*((mask>>i)&1)-1 for i in range(15)] for mask in range(1<<15)],float)
    vals=[]
    for sign in [-1,1]:
        for t in [-1,1]:
            zz=np.column_stack([sign*z,np.full(len(z),t)])
            den=1+zz@B;num=zz@U
            assert np.min(den)>0
            vals.append(T*np.prod(den,axis=1)+np.sum(num*np.prod(den,axis=1)[:,None]/den,axis=1))
    vals=np.array(vals).T;times=np.array([-1,1,-1,1.])
    q=np.mean(vals*times,axis=1);y=np.sign(q)
    valid=np.all(vals*times*y[:,None]>0,axis=1)
    if actual:z=z[valid];y=y[valid]
    pairs=list(itertools.combinations(range(16),2))
    features=np.column_stack([np.ones(len(z))]+[z[:,i]*z[:,j] for i,j in pairs])
    return z,y,features,pairs,int(np.sum(valid)),q


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seed-file',default='artifacts/rope/four_head_middle/seed_zero_t_linear.json');ap.add_argument('--projected-only',action='store_true');ap.add_argument('--max-tests',type=int,default=64);ap.add_argument('--out',default='/tmp/quadratic_sign_cone.jsonl');args=ap.parse_args()
    r,S,B,U,T=load(args.seed_file);z,y,F,pairs,consistent,q=data(S,B,U,T,not args.projected_only)
    print('spatial orbits',len(z),'actual consistent',consistent,'projected sign balance',int(np.sum(q>0)),int(np.sum(q<0)),flush=True)
    if not len(z):return
    start=time.time();constraints=-y[:,None]*F;rhs=-np.ones(len(y));targets=[]
    for i in range(8):
        for j in range(8):
            if i==j:continue
            obj=np.zeros(F.shape[1]);obj[1+pairs.index(tuple(sorted((2*i,2*j+1))))]=1
            targets.append(('offdiag',i,j,obj))
    for j in range(8):
        obj=np.zeros(F.shape[1])
        for i in range(8):obj[1+pairs.index(tuple(sorted((2*i,2*j+1))))]=-1
        targets.append(('column',j,None,obj))
    for kind,i,j,obj in targets[:args.max_tests]:
        # Find a strict sign polynomial violating the proposed coefficient sign.
        A=np.vstack([constraints,-obj]);b=np.r_[rhs,0.]
        lp=linprog(np.zeros(F.shape[1]),A_ub=A,b_ub=b,bounds=[(None,None)]*F.shape[1],method='highs',options={'time_limit':60})
        rec={'kind':kind,'i':i,'j':j,'status':lp.status,'message':lp.message,'seconds':time.time()-start,'orbits':len(z)}
        if lp.success:rec['witness']=lp.x.tolist()
        with Path(args.out).open('a') as f:f.write(json.dumps(rec)+'\n')
        print({k:v for k,v in rec.items() if k!='witness'},flush=True)


if __name__=='__main__':main()
