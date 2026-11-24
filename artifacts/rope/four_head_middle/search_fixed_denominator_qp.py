"""Squared-margin variable projection for actual pure-four scores.

Exploratory only. OSQP proposals are never accepted as exact certificates.
Run with heavy. This complements the nonsmooth fixed-denominator LP search.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
import osqp
from scipy import sparse
from scipy.optimize import minimize
from search_fixed_denominator_lp import Z,Y,X,N,H,NV,ELL,K,BASE,encode,solve


def solve_qp(beta,signs,regularizer=1e-10,warm=None):
    d=1+Z@beta.T;count=len(Y);width=BASE+count
    rows=[];rhs=[]
    for j in range(count):
        row=np.zeros(width)
        for h in range(H):row[h*(N+1):(h+1)*(N+1)]=-Y[j]*X[j]/d[j,h]
        row[BASE+j]=-1;rows.append(row);rhs.append(-1)
    for h in range(H):
        for i in range(N):
            row=np.zeros(width);row[h*(N+1)+i+1]=-signs[h]
            row[ELL+h]=beta[h,i];row[K+h]=abs(beta[h,i])
            rows.append(row);rhs.append(-1e-7)
        row=np.zeros(width);row[h*(N+1)+1:(h+1)*(N+1)]=signs[h]
        row[ELL+h]=-sum(beta[h]);row[K+h]=-1;rows.append(row);rhs.append(-1e-7)
    main=len(rows)
    for index in list(range(K,BASE))+list(range(BASE,width)):
        row=np.zeros(width);row[index]=-1;rows.append(row);rhs.append(-1e-7 if index<BASE else 0)
    A=sparse.csc_matrix(np.array(rows));rhs=np.array(rhs)
    diag=np.r_[np.full(NV,2*regularizer),np.zeros(2*H),np.full(count,2/count)]
    solver=osqp.OSQP();solver.setup(P=sparse.diags(diag,format='csc'),q=np.zeros(width),
        A=A,l=np.full(len(rows),-np.inf),u=rhs,verbose=False,eps_abs=1e-7,
        eps_rel=1e-7,max_iter=10000,polishing=True,time_limit=3)
    if warm is not None:solver.warm_start(x=warm)
    result=solver.solve(raise_error=False)
    if result.x is None:return None
    theta=result.x;violation=np.max(A@theta-rhs)
    if violation>1e-3:return None
    num=X@theta[:NV].reshape(H,N+1).T;score=np.sum(num/d,axis=1);margin=Y*score
    mu=result.y[:main];grad=np.zeros_like(beta)
    for h in range(H):
        grad[h]=np.sum((mu[:count]*Y*num[:,h]/d[:,h]**2)[:,None]*Z,axis=0)
        offset=count+h*(N+1)
        grad[h]+=mu[offset:offset+N]*(theta[ELL+h]+theta[K+h]*np.sign(beta[h]))
        grad[h]-=mu[offset+N]*theta[ELL+h]
    loss=float(np.mean(theta[BASE:]**2)+regularizer*np.sum(theta[:NV]**2))
    return {'loss':loss,'gradient':grad,'warm':theta,'minimum_margin':float(min(margin)),
        'errors':int(sum(margin<=0)),'beta':beta.tolist(),'signs':list(map(int,signs)),
        'numerators':theta[:NV].reshape(H,N+1).tolist(),
        'ell_signed':theta[ELL:K].tolist(),'k_absolute':theta[K:BASE].tolist(),
        'qp_status':str(result.info.status),'maximum_constraint_violation':float(violation)}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seed-file',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True);ap.add_argument('--restarts',type=int,default=12)
    ap.add_argument('--iterations',type=int,default=400);ap.add_argument('--sign-mask',type=int,default=2)
    ap.add_argument('--regularizer',type=float,default=1e-10);a=ap.parse_args()
    rng=np.random.default_rng(996234);beta=np.array(json.loads(a.seed_file.read_text())['beta'])
    signs=np.array([-1 if a.sign_mask>>h&1 else 1 for h in range(H)])
    for restart in range(a.restarts):
        b=beta.copy()
        if restart:b+=rng.normal(0,.003*restart,b.shape)
        b*=min(1,.98/max(np.sum(abs(b),axis=1)))
        v=b/(1-np.sum(abs(b),axis=1,keepdims=True));best=[None];warm=[None];calls=[0]
        start=time.time()
        def fg(flat):
            v=flat.reshape(H,N);b,den=encode(v)
            fit=solve_qp(b,signs,a.regularizer,warm[0]);calls[0]+=1
            if fit is None:return 1e10,np.zeros_like(flat)
            g=fit.pop('gradient');warm[0]=fit.pop('warm')
            if best[0] is None or fit['loss']<best[0]['loss']:best[0]=fit
            gv=(g-np.sum(g*v,axis=1,keepdims=True)*v/np.sqrt(v*v+1e-16)/den)/den
            return fit['loss'],gv.ravel()
        result=minimize(fg,v.ravel(),jac=True,method='L-BFGS-B',
            options={'maxiter':a.iterations,'ftol':1e-13,'gtol':1e-7,'maxls':25})
        fit=best[0]
        if fit:
            fit.update({'status':'numerical proposal only','restart':restart,'seconds':time.time()-start,'calls':calls[0]})
            lp=solve(np.array(fit['beta']),signs,False)
            if lp and lp['success']:fit['feasible_lp']=lp
            with a.out.open('a') as out:out.write(json.dumps(fit)+'\n')
            print({k:fit[k] for k in ['restart','loss','minimum_margin','errors','seconds','calls']},flush=True)
            if 'feasible_lp' in fit:
                print('FULL LOCAL PURE SCORE LP PROPOSAL FOUND; EXACT VERIFICATION REQUIRED',flush=True);break


if __name__=='__main__':main()
