"""Eliminate affine numerators before optimizing vanilla denominators.

The orthonormal feature basis avoids penalizing large cancelling numerator
coefficients. Numerical outcomes have no proof status until the shared integer
verifier accepts a rational certificate. Run through heavy.
"""
import argparse
import json
from pathlib import Path
import time


def fit(record, restarts, seed, maxiter):
    import numpy as np
    from scipy.optimize import minimize
    from search_many_head import vertices, endpoint_biases, rationalize
    n, heads = record['n'], record['heads']
    Z=vertices(n); X=np.column_stack([np.ones(len(Z)),Z])
    truth=int(record['pure_certificate']['truth_table'],16)
    y=np.array([1.0 if (truth>>i)&1 else -1.0 for i in range(len(Z))])
    rng=np.random.default_rng(seed)
    best=1e100
    for restart in range(restarts):
        signs=np.array([-1.0 if h<restart%(heads+1) else 1.0 for h in range(heads)])
        initial=rng.normal(size=(heads,n+1))*1.8
        if restart%(heads+2)==0:
            B=endpoint_biases(record['pure_certificate'])
            signs=np.sign(B[:,0]); initial=np.log(np.column_stack([1-abs(B).sum(axis=1),abs(B)]))
        previous_prediction=y.copy()
        latest={}
        calls=0
        def objective(raw):
            nonlocal previous_prediction,calls
            L=raw.reshape(heads,n+1)
            W=np.exp(L-L.max(axis=1,keepdims=True));W/=W.sum(axis=1,keepdims=True)
            B=signs[:,None]*W[:,1:]
            D=1+Z@B.T
            cof=np.column_stack([np.prod(np.delete(D,h,axis=1),axis=1) for h in range(heads)])
            F=np.column_stack([X*cof[:,h,None] for h in range(heads)])
            U,s,V=np.linalg.svd(F,full_matrices=False)
            rank=int(np.sum(s>1e-13*s[0])); U=U[:,:rank]
            regularizer=1e-10
            def linear_obj(a):
                P=U@a; gap=np.minimum(y*P-1,0)
                gp=2*(gap*y+regularizer*P)/len(y)
                return (gap@gap+regularizer*(P@P))/len(y), U.T@gp
            init=U.T@previous_prediction
            inner=minimize(linear_obj,init,jac=True,method='L-BFGS-B',options={'maxiter':500,'ftol':1e-14,'gtol':1e-11})
            P=U@inner.x;previous_prediction=P
            A=(V[:rank].T@(inner.x/s[:rank])).reshape(heads,n+1)
            N=X@A.T
            gap=np.minimum(y*P-1,0);gp=2*(gap*y+regularizer*P)/len(y)
            gB=np.zeros((heads,n))
            for h in range(heads):
                dP=sum(N[:,j]*np.prod(np.delete(D,[h,j],axis=1),axis=1) for j in range(heads) if j!=h)
                gB[h]=Z.T@(gp*dP)
            gW=np.column_stack([np.zeros(heads),signs[:,None]*gB])
            gL=W*(gW-np.sum(gW*W,axis=1,keepdims=True))
            latest.update(B=B.tolist(),loss=float(inner.fun),minimum=float(np.min(y*P)),rank=rank)
            calls+=1
            return inner.fun,gL.ravel()
        result=minimize(objective,initial.ravel(),jac=True,method='L-BFGS-B',options={'maxiter':maxiter,'ftol':1e-13,'gtol':1e-9,'maxls':30})
        objective(result.x)
        best=min(best,latest['loss'])
        candidate=dict(record); candidate['vanilla_search']={'status':'floating_fit','B':latest['B']}
        exact=rationalize(candidate,Z,y)
        print('sample',record['sample'],'restart',restart,'loss',latest['loss'],'minimum',latest['minimum'],'calls',calls,'exact',exact is not None,flush=True)
        if exact:return exact
    return None


def main():
    parser=argparse.ArgumentParser();parser.add_argument('source')
    parser.add_argument('--samples',default='9');parser.add_argument('--restarts',type=int,default=8)
    parser.add_argument('--maxiter',type=int,default=200);parser.add_argument('--seed',type=int,default=2026112430)
    args=parser.parse_args();samples={int(v) for v in args.samples.split(',')}
    path=Path(args.source);out=path.with_suffix('.projection.exact.jsonl')
    for line in path.read_text().splitlines():
        record=json.loads(line)
        if record['sample'] not in samples:continue
        start=time.monotonic();exact=fit(record,args.restarts,args.seed+record['sample'],args.maxiter)
        if exact:
            with out.open('a') as target:target.write(json.dumps(exact,separators=(',',':'))+'\n')
        print('completed',record['sample'],'seconds',time.monotonic()-start,'certified',exact is not None,flush=True)


if __name__=='__main__':main()
