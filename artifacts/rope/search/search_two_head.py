"""Exploratory search only. Failure to fit is never a lower-bound certificate.
Run with heavy python3 artifacts/rope/search/search_two_head.py.
"""
import argparse, json, time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog, minimize


def vertices(n):
    return np.array([[2 * ((k >> i) & 1) - 1 for i in range(n)] for k in range(1 << n)], float)


def fit_vanilla(Z, y, restarts, rng):
    n = Z.shape[1]
    X = np.column_stack([np.ones(len(Z)), Z])
    best = float('inf')
    for restart in range(restarts):
        signs = np.array([1., 1. if restart % 2 else -1.])
        def fg(theta):
            L = theta[:2*(n+1)].reshape(2,n+1)
            L = L - np.max(L, axis=1, keepdims=True)
            W = np.exp(L); W /= W.sum(axis=1, keepdims=True)
            B = signs[:,None] * W[:,1:]
            D = 1 + Z @ B.T
            A = theta[2*(n+1):].reshape(2,n+1)
            N = X @ A.T
            P = N[:,0]*D[:,1] + N[:,1]*D[:,0]
            gap = np.minimum(y*P - 1, 0)
            reg = 1e-9
            loss = np.mean(gap**2) + reg*np.sum(A*A)
            gp = 2*gap*y/len(y)
            gA = np.stack([X.T@(gp*D[:,1]), X.T@(gp*D[:,0])]) + 2*reg*A
            gB = np.stack([Z.T@(gp*N[:,1]), Z.T@(gp*N[:,0])])
            gW = np.column_stack([np.zeros(2), signs[:,None]*gB])
            gL = W*(gW - np.sum(gW*W,axis=1,keepdims=True))
            return loss, np.concatenate([gL.ravel(),gA.ravel()])
        theta = rng.normal(size=4*(n+1))
        theta[:2*(n+1)] *= 2
        res = minimize(fg, theta, jac=True, method='L-BFGS-B', options={'maxiter':2000,'ftol':1e-13,'gtol':1e-8})
        best = min(best,res.fun)
        L = res.x[:2*(n+1)].reshape(2,n+1)
        W = np.exp(L - L.max(axis=1,keepdims=True)); W /= W.sum(axis=1,keepdims=True)
        B = signs[:,None]*W[:,1:]
        D = 1 + Z @ B.T
        F = np.column_stack([X*D[:,1,None],X*D[:,0,None]])
        lp = linprog(np.zeros(2*(n+1)), A_ub=-y[:,None]*F, b_ub=-np.ones(len(y)), bounds=[(None,None)]*(2*(n+1)), method='highs')
        if lp.success and np.min(y*(F@lp.x)) > .9:
            return {'status':'floating_fit','restarts':restart+1,'loss':float(best),'B':B.tolist(),'numerators':lp.x.reshape(2,n+1).tolist()}
    return {'status':'unresolved','restarts':restarts,'loss':float(best)}


def random_pure(Z, rng):
    n = Z.shape[1]
    # Integer attention weights and integer values make exact certificates easy.
    a = np.rint(np.exp(rng.uniform(0,7,(2,n)))).astype(int)
    b = np.rint(np.exp(rng.uniform(0,7,(2,n)))).astype(int)
    gamma = rng.integers(1,20,2)
    values = rng.integers(-8,9,(2,3))
    X = ((Z+1)/2).astype(int)
    D = gamma + (1-X)@a.T + X@b.T
    N = gamma*values[:,2] + (1-X)@(a*values[:,0,None]).T + X@(b*values[:,1,None]).T
    S = np.sum(N/D,axis=1)
    # Exact rational threshold picked near the middle of the distinct scores.
    c_den = 1000000
    c_num = -int(round(float(np.quantile(S,rng.uniform(.2,.8)))*c_den))
    P = c_num*D[:,0]*D[:,1] + c_den*(N[:,0]*D[:,1]+N[:,1]*D[:,0])
    if np.any(P == 0): return random_pure(Z,rng)
    y = np.sign(P)
    return y, {'a':a.tolist(),'b':b.tolist(),'gamma':gamma.tolist(),'values':values.tolist(),'constant':[c_num,c_den], 'truth_table':hex(sum(int(v>0)<<i for i,v in enumerate(y))),'minimum_cleared_margin':int(np.min(np.abs(P)))}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--n',type=int,default=8); ap.add_argument('--samples',type=int,default=100); ap.add_argument('--restarts',type=int,default=10); ap.add_argument('--seed',type=int,default=20261124); args=ap.parse_args()
    rng=np.random.default_rng(args.seed); Z=vertices(args.n)
    out=Path(f'artifacts/rope/search/random_pure_n{args.n}_{args.seed}.jsonl')
    for i in range(args.samples):
        y, cert=random_pure(Z,rng); t=time.time()
        fit=fit_vanilla(Z,y,args.restarts,rng)
        result={'sample':i,'n':args.n,'pure_certificate':cert,'vanilla_search':fit,'seconds':time.time()-t}
        with out.open('a') as f: f.write(json.dumps(result)+'\n')
        print(i,fit['status'],fit['restarts'],fit['loss'],round(result['seconds'],2),flush=True)

if __name__=='__main__': main()
