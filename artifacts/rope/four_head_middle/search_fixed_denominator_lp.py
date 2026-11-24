"""Full pure-four local-score search by variable projection.

For fixed positive denominators and fixed signs of token-value contrasts,
both the pure-atom constraints and all score labels are linear. Numerical
results are proposals only; a separation requires exact full-cube checking.
Run substantial searches with heavy.
"""
import argparse
from fractions import Fraction
import itertools
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import linprog, minimize
from search_projected_pattern import pattern


def full_pattern():
    z,y=pattern();data={}
    for zz,yy in zip(z,y):
        for flip in [-1,1]:
            for t in [-1,1]:
                row=tuple([t]+list(flip*zz));label=t*yy
                assert row not in data or data[row]==label
                data[row]=label
    assert len(data)==364
    return np.array(list(data)),np.array(list(data.values()))


Z,Y=full_pattern();X=np.c_[np.ones(len(Z)),Z]
N=17;H=4;NV=H*(N+1);ELL=NV;K=ELL+H;BASE=K+H
HARD_MASK = None


def solve(beta,signs,soft=False,regularizer=1e-8):
    """LP, plus exact envelope derivative with respect to fixed beta."""
    d=1+Z@beta.T
    if np.min(d)<=0:return None
    count=len(Y);width=BASE+(count+2*NV if soft else 0)
    rows=[];rhs=[]
    for j in range(count):
        row=np.zeros(width)
        for h in range(H):row[h*(N+1):(h+1)*(N+1)]=-Y[j]*X[j]/d[j,h]
        if soft:row[BASE+j]=-1
        rows.append(row);rhs.append(-1)
    for h in range(H):
        for i in range(N):
            row=np.zeros(width);row[h*(N+1)+i+1]=-signs[h]
            row[ELL+h]=beta[h,i];row[K+h]=abs(beta[h,i])
            rows.append(row);rhs.append(-1e-7)
        row=np.zeros(width);row[h*(N+1)+1:(h+1)*(N+1)]=signs[h]
        row[ELL+h]=-sum(beta[h]);row[K+h]=-1
        rows.append(row);rhs.append(-1e-7)
    bounds=[(None,None)]*NV+[(None,None)]*H+[(1e-7,None)]*H
    objective=np.zeros(width)
    if soft:
        bounds += [(0,None)]*count+[(0,None)]*(2*NV)
        if HARD_MASK is not None:
            for j in np.flatnonzero(HARD_MASK):
                bounds[BASE+j] = (0,0)
        objective[BASE:BASE+count]=1/count
        objective[BASE+count:]=regularizer
        # Numerators are a difference of two nonnegative parts.
        aeq=np.zeros((NV,width))
        for i in range(NV):
            aeq[i,i]=1;aeq[i,BASE+count+i]=-1;aeq[i,BASE+count+NV+i]=1
    else:aeq=None
    A=np.array(rows);rhs=np.array(rhs)
    result=linprog(objective,A_ub=A,b_ub=rhs,A_eq=aeq,
                   b_eq=np.zeros(NV) if soft else None,bounds=bounds,method='highs',options={'time_limit':5.0})
    if not result.success:return {'success':False,'message':result.message}
    theta=result.x;num=(X@theta[:NV].reshape(H,N+1).T)
    score=np.sum(num/d,axis=1);margin=Y*score
    output={'success':True,'loss':float(result.fun),'minimum_margin':float(min(margin)),
            'errors':int(sum(margin<=0)),'beta':beta.tolist(),'signs':list(map(int,signs)),
            'numerators':theta[:NV].reshape(H,N+1).tolist(),
            'ell_signed':theta[ELL:K].tolist(),'k_absolute':theta[K:BASE].tolist()}
    if soft:
        mu=-result.ineqlin.marginals
        grad=np.zeros_like(beta)
        for h in range(H):
            grad[h]=np.sum((mu[:count]*Y*num[:,h]/d[:,h]**2)[:,None]*Z,axis=0)
            offset=count+h*(N+1)
            grad[h]+=mu[offset:offset+N]*(theta[ELL+h]+theta[K+h]*np.sign(beta[h]))
            grad[h]-=mu[offset+N]*theta[ELL+h]
        output['gradient']=grad
    return output


def encode(v):
    # Every row has absolute sum less than one, including during line search.
    denom=1+np.sum(np.sqrt(v*v+1e-16),axis=1,keepdims=True)
    return v/denom,denom


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seed-file',type=Path)
    ap.add_argument('--out',type=Path,required=True);ap.add_argument('--restarts',type=int,default=16)
    ap.add_argument('--iterations',type=int,default=600);ap.add_argument('--seed',type=int,default=880123)
    ap.add_argument('--regularizer',type=float,default=1e-8);a=ap.parse_args()
    rng=np.random.default_rng(a.seed);beta0=None
    if a.seed_file:
        obj=json.loads(a.seed_file.read_text())
        if 'beta' in obj:beta0=np.array(obj['beta'],float)
        elif 'B' in obj:
            beta0=np.array([[float(Fraction(t)) for t in row] for row in obj['B']]).T
    for restart in range(a.restarts):
        signs=np.array([-1 if restart>>h&1 else 1 for h in range(H)])
        if beta0 is None:v=rng.normal(0,.05,(H,N))
        else:
            b=beta0.copy()
            if restart >= (1 << H):b+=rng.normal(0,.005,b.shape)
            b*=min(1,.95/max(np.sum(abs(b),axis=1)))
            v=b/(1-np.sum(abs(b),axis=1,keepdims=True))
        best=[None];calls=[0];start=time.time()
        def fg(flat):
            v=flat.reshape(H,N);b,den=encode(v)
            fit=solve(b,signs,True,a.regularizer);calls[0]+=1
            if not fit or not fit['success']:return 1e10,np.zeros(flat.shape)
            g=fit.pop('gradient')
            if best[0] is None or fit['loss']<best[0]['loss']:best[0]=fit
            gv=(g-np.sum(g*v,axis=1,keepdims=True)*v/np.sqrt(v*v+1e-16)/den)/den
            return fit['loss'],gv.ravel()
        result=minimize(fg,v.ravel(),jac=True,method='L-BFGS-B',
                        options={'maxiter':a.iterations,'ftol':1e-14,'gtol':1e-8,'maxls':40})
        fit=best[0]
        if fit:
            fit.update({'status':'numerical proposal only','restart':restart,'seconds':time.time()-start,
                        'calls':calls[0],'optimizer_message':str(result.message)})
            exactlp=solve(np.array(fit['beta']),signs,False)
            if exactlp and exactlp['success']:fit['feasible_lp']=exactlp
            with a.out.open('a') as out:out.write(json.dumps(fit)+'\n')
            print({k:fit[k] for k in ['restart','loss','minimum_margin','errors','seconds','calls']},flush=True)
            if 'feasible_lp' in fit:
                print('FULL LOCAL PURE SCORE LP PROPOSAL FOUND; EXACT VERIFICATION REQUIRED',flush=True)
                break


if __name__=='__main__':main()
