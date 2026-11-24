"""Explore an admissible coordinate embedding of the four-head cubic matrix.

This does not fit Boolean signs or prove a lower bound. Heavy computation:
  heavy python3 .../search_embedding.py --seed-file ... --out /tmp/embedding.jsonl
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import minimize
import torch

torch.set_default_dtype(torch.float64)
torch.set_num_threads(1)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seed-file',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--restarts',type=int,default=16);ap.add_argument('--maxiter',type=int,default=5000);a=ap.parse_args()
    obj=json.loads(a.seed_file.read_text());mat=lambda v:np.array([[float(Fraction(t)) for t in r] for r in v])
    H=mat(obj['H_unscaled']); Hi=np.linalg.inv(H);C=np.eye(8)-.001*np.ones((8,8)); ht=torch.tensor(H);hit=torch.tensor(Hi);ct=torch.tensor(C)
    rng=np.random.default_rng(28221)
    orig=[mat(obj['Y_unscaled']),mat(obj['X_unscaled'])]
    for j in range(a.restarts):
        init=orig[j%2];S=init[:,:4]; B=init[:,4:];S=S/S.sum(axis=1,keepdims=True);B=B/init[:,:4].sum(axis=1,keepdims=True)
        theta=np.r_[np.log(S).ravel(),np.arctanh(B/S).ravel()]
        if j>=2:theta+=rng.normal(0,.1*(1+j//2),theta.shape)
        def fg(p):
            v=torch.tensor(p,requires_grad=True);s=torch.softmax(v[:32].reshape(8,4),dim=1);b=s*torch.tanh(v[32:].reshape(8,4));Y=torch.cat([s,b],dim=1)
            X=ct@torch.linalg.inv(Y.T)@hit
            xn=X/torch.linalg.vector_norm(X,dim=1,keepdim=True)
            cone=torch.cat([xn[:,:4]+xn[:,4:],xn[:,:4]-xn[:,4:]],dim=1)
            G=Y@ht@Y.T
            norms=torch.linalg.vector_norm(Y,dim=1);G=G/(norms[:,None]*norms[None,:]*np.linalg.norm(H,2))
            off=G[~torch.eye(8,dtype=torch.bool)]
            loss=torch.mean(torch.relu(.0001-cone)**2)+torch.mean(torch.relu(.00001+off)**2)
            loss.backward()
            return loss.item(),v.grad.detach().numpy()
        start=time.time();r=minimize(fg,theta,jac=True,method='L-BFGS-B',options={'maxiter':a.maxiter,'ftol':1e-18,'gtol':1e-11,'maxls':50})
        p=r.x;ex=np.exp(p[:32].reshape(8,4));S=ex/ex.sum(axis=1,keepdims=True);B=S*np.tanh(p[32:].reshape(8,4));Y=np.c_[S,B];X=C@np.linalg.inv(Y.T)@Hi;G=Y@H@Y.T
        result={'status':'coefficient embedding only; no Boolean signs','restart':j,'loss':float(r.fun),'iterations':r.nit,'seconds':time.time()-start,'minimum_X_cone_gap':float(np.min(X[:,:4]-np.abs(X[:,4:]))),'maximum_Y_gram_offdiagonal':float(np.max(G[~np.eye(8,dtype=bool)])),'X':X.tolist(),'Y':Y.tolist()}
        with a.out.open('a') as f:f.write(json.dumps(result)+'\n')
        print({k:v for k,v in result.items() if k not in ['X','Y']},flush=True)
        if result['minimum_X_cone_gap']>0 and result['maximum_Y_gram_offdiagonal']<0:
            print('FLOATING EMBEDDING FEASIBLE; EXACT VERIFICATION AND BOOLEAN LABELS REMAIN.',flush=True);break

if __name__=='__main__':main()
