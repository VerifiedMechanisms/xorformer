#!/usr/bin/env python3
"""Exploratory original-head margin optimization; numerical, never a proof.

For fixed positive coherent denominators, solve the exact full-cube epigraph LP
for arbitrary affine numerators and bias. Optimize denominator logits using its
dual-envelope derivative. Every reported certificate is checked again directly,
then each head is midrange centered. All cube rows enter the norm and margin.
"""
import argparse
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import linprog, minimize
from scipy.special import softmax


def cube(n):
    return np.array([[(i >> j) & 1 for j in range(n)] for i in range(2**n)], dtype=float)


class MarginLP:
    def __init__(self, x, labels, h, orientation, hinge_goal=None):
        self.x = x
        self.f = np.asarray(labels, dtype=float)
        self.h = h
        self.n = x.shape[1]
        self.d = self.n + 1
        self.N = len(x)
        self.z = np.column_stack([np.ones(self.N), x])
        self.orientation = np.asarray(orientation, dtype=int)
        self.den_z = np.stack([np.column_stack([np.ones(self.N), x if o > 0 else 1-x]) for o in orientation])
        self.ncoef = h*self.d
        self.ib = self.ncoef
        self.it = self.ib+1
        self.itb = self.it+h
        self.ig = self.itb+1
        self.p = self.ig+1
        self.calls = 0
        self.hinge_goal = hinge_goal

    def solve(self, theta, details=False):
        self.calls += 1
        w = softmax(np.reshape(theta, (self.h, self.d)), axis=1)
        B = np.einsum('hij,hj->hi', self.den_z, w)
        features = self.z[None, :, :] / B[:, :, None]
        mat = np.zeros((self.N*(1+2*self.h)+3, self.p))
        mat[:self.N, :self.ncoef] = -self.f[:,None]*features.transpose(1,0,2).reshape(self.N,self.ncoef)
        mat[:self.N, self.ib] = -self.f
        mat[:self.N, self.ig] = 1
        for head in range(self.h):
            a = self.N + 2*head*self.N
            sl = slice(head*self.d, (head+1)*self.d)
            mat[a:a+self.N, sl] = features[head]
            mat[a+self.N:a+2*self.N, sl] = -features[head]
            mat[a:a+2*self.N, self.it+head] = -1
        mat[-3, self.ib] = 1
        mat[-3, self.itb] = -1
        mat[-2, self.ib] = -1
        mat[-2, self.itb] = -1
        mat[-1, self.it:self.itb+1] = 1
        rhs = np.zeros(len(mat)); rhs[-1] = 1
        obj = np.zeros(self.p); obj[self.ig] = -1
        bounds = [(None,None)]*(self.ib+1)+[(0,None)]*(self.h+1)+[(None,None)]
        if self.hinge_goal is not None:
            extra=np.zeros((len(mat),self.N)); extra[:self.N,:]=-np.eye(self.N)
            mat=np.column_stack([mat,extra])
            obj=np.concatenate([np.zeros(self.p),np.ones(self.N)/self.N])
            bounds[self.ig]=(self.hinge_goal,self.hinge_goal)
            bounds += [(0,None)]*self.N
        sol = linprog(obj, A_ub=mat, b_ub=rhs, bounds=bounds, method='highs',
                      options={'primal_feasibility_tolerance':1e-9, 'dual_feasibility_tolerance':1e-9})
        if not sol.success:
            raise RuntimeError(sol.message)
        coef = sol.x[:self.ncoef].reshape(self.h,self.d)
        A = coef @ self.z.T
        vals = A/B
        grad = np.zeros_like(w)
        dual = sol.ineqlin.marginals
        for head in range(self.h):
            a = self.N + 2*head*self.N
            factor = (self.f*dual[:self.N]-dual[a:a+self.N]+dual[a+self.N:a+2*self.N])*A[head]/B[head]**2
            grad[head] = np.einsum('i,ij,j->j', factor, self.den_z[head]-B[head,:,None], w[head])
        if not details:
            return float(sol.fun), -grad.ravel()
        bias = float(sol.x[self.ib])
        centers = (vals.max(axis=1)+vals.min(axis=1))/2
        centered = vals-centers[:,None]
        cbias = bias+float(centers.sum())
        score = cbias+centered.sum(axis=0)
        amplitude = abs(cbias)+np.abs(centered).max(axis=1).sum()
        gap = float(np.min(self.f*score))
        pairdist = min((float(np.linalg.norm(w[i]-w[j])) for i in range(self.h) for j in range(i)), default=None)
        return {'lp_margin':float(sol.x[self.ig]), 'objective':float(sol.fun), 'checked_margin': gap/amplitude if amplitude>0 else 0.,
                'gap':gap, 'amplitude':float(amplitude), 'weights':w.tolist(),
                'numerators':coef.tolist(), 'bias':bias, 'centered_bias':cbias,
                'centers':centers.tolist(), 'orientation':self.orientation.tolist(),
                'score':score.tolist(), 'pair_weight_distance':pairdist,
                'max_constraint_violation':float(np.max(mat@sol.x-rhs))}


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--n',type=int,default=5)
    ap.add_argument('--heads',type=int,default=2)
    ap.add_argument('--targets',type=int,default=32)
    ap.add_argument('--restarts',type=int,default=8)
    ap.add_argument('--iterations',type=int,default=80)
    ap.add_argument('--seed',type=int,default=177)
    ap.add_argument('--output',required=True)
    ap.add_argument('--random-labels',action='store_true')
    args=ap.parse_args()
    rng=np.random.default_rng(args.seed); x=cube(args.n); z=np.column_stack([np.ones(len(x)),x])
    results=[]; seen=set(); started=time.time()
    while len(results)<args.targets:
        # Realize labels using genuine original heads; alternating ordinary and
        # heavily unbalanced denominators probes different initial geometries.
        scale=[1.,3.,8.,16.][len(results)%4]
        theta=rng.normal(0,scale,(args.heads,args.n+1))
        orient=rng.choice([-1,1],args.heads)
        w=softmax(theta,axis=1)
        den=np.stack([np.column_stack([np.ones(len(x)),x if o>0 else 1-x])@wh for o,wh in zip(orient,w)])
        a=rng.normal(size=(args.heads,args.n+1))
        raw=(a@z.T)/den
        raw=(raw-(raw.max(axis=1)+raw.min(axis=1))[:,None]/2)
        raw/=np.maximum(np.abs(raw).max(axis=1)[:,None],1e-30)
        score=raw.sum(axis=0)
        bias=-float(np.quantile(score,rng.uniform(.25,.75)))+rng.uniform(-1e-5,1e-5)
        labels=rng.choice([-1,1],len(x)) if args.random_labels else np.where(score+bias>0,1,-1)
        key=''.join('+' if t>0 else '-' for t in labels)
        if key in seen: continue
        seen.add(key)
        best=None; runs=[]
        for restart in range(args.restarts):
            thisorient=orient if restart==0 else rng.choice([-1,1],args.heads)
            start=theta.copy() if restart==0 else rng.normal(0,[.3,1.,3.][restart%3],theta.shape)
            start-=start.mean(axis=1)[:,None]
            start=np.clip(start,-6,6)
            lp=MarginLP(x,labels,args.heads,thisorient)
            initial=lp.solve(start.ravel(),True)
            error=None
            try:
                opt=minimize(lp.solve,start.ravel(),method='L-BFGS-B',jac=True,
                             bounds=[(-6,6)]*start.size,
                             options={'maxiter':args.iterations,'ftol':1e-12,'gtol':1e-8,'maxls':30})
                checked=lp.solve(opt.x,True)
            except RuntimeError as exc:
                from types import SimpleNamespace
                error=str(exc)
                opt=SimpleNamespace(x=start.ravel(),nit=0,success=False)
                checked=initial
            if initial['checked_margin']>checked['checked_margin']:
                checked=initial; chosen=start.ravel()
            else: chosen=opt.x
            checked['theta']=chosen.tolist()
            runs.append({'initial':initial['checked_margin'],'final':checked['checked_margin'],
                         'calls':lp.calls,'iterations':opt.nit,'success':bool(opt.success),'solver_error':error})
            if best is None or checked['checked_margin']>best['checked_margin']: best=checked
        if args.random_labels and best['checked_margin']<1e-7:
            continue
        results.append({'index':len(results),'labels':key,'witness_scale':scale,'best':best,'runs':runs})
        out={'status':'numerical exploration, not an upper bound on optimal margin',
             'config':vars(args),'candidate_count':len(seen),'elapsed_seconds':time.time()-started,'results':results}
        Path(args.output).write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps({'target':len(results),'best_margin':best['checked_margin'],
                          'min_best_so_far':min(r['best']['checked_margin'] for r in results),
                          'pair_distance':best['pair_weight_distance'],'seconds':time.time()-started}),flush=True)

if __name__=='__main__': main()
