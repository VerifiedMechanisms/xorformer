"""Preserve a successful split quadratic while seeking a pure-cone embedding.

This is a projected relaxation: it does not solve the selector lift or certify
any Boolean head-count separation. Runs through ``heavy python3``.
"""
import argparse,json,time
from pathlib import Path
from fractions import Fraction
import numpy as np
import torch
from scipy.optimize import minimize


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--embedding',default='/tmp/positive_functional_middle_embedding.json');ap.add_argument('--seed-file',default='artifacts/rope/four_head_middle/seed_zero_t_linear.json');ap.add_argument('--out',default='/tmp/projected_isometry.jsonl');ap.add_argument('--restarts',type=int,default=24);args=ap.parse_args()
    torch.set_num_threads(1)
    emb=json.loads(Path(args.embedding).read_text());v=np.array(emb['theta'][:-1]).reshape(16,8);v[:,0]=np.exp(v[:,0]);r=json.loads(Path(args.seed_file).read_text());H=np.array([[float(Fraction(x)) for x in row] for row in r['H_unscaled']])
    vals,vecs=np.linalg.eigh(H);order=np.r_[np.where(vals>0)[0],np.where(vals<0)[0]];vals=vals[order];vecs=vecs[:,order];assert np.sum(vals>0)==4
    R=vecs*np.sqrt(abs(vals))[None,:];Rinv=np.linalg.inv(R)
    J=np.diag([1.]*4+[-1.]*4);assert np.max(abs(R@J@R.T-H))<1e-8
    a=Rinv[:,0]
    w=np.array(emb.get('positive_functional',[1.,0,0,0,0,0,0,0]))
    if w@J@w<=0:w=np.array([1.,0,0,0,0,0,0,0])
    target=w*np.sqrt((a@J@a)/(w@J@w))
    diff=a-target
    O0=np.eye(8)-2*np.outer(diff,diff@J)/(diff@J@diff)
    assert np.max(abs(O0@a-target))<1e-8
    assert np.max(abs(O0@J@O0.T-J))<1e-7
    vt=torch.tensor(v,dtype=torch.float64);rt=torch.tensor(O0@Rinv,dtype=torch.float64);jt=torch.tensor(J,dtype=torch.float64)
    upper=torch.triu_indices(8,8,1)
    def objective(th):
        p=torch.tensor(th,dtype=torch.float64,requires_grad=True);K=torch.zeros((8,8),dtype=torch.float64);K[upper[0],upper[1]]=p;K=K-K.T
        O=torch.matrix_exp(jt@K);w=vt@O@rt
        cone=torch.cat([w[:,:4]-w[:,4:],w[:,:4]+w[:,4:]],dim=1)/torch.linalg.vector_norm(w,dim=1)[:,None]
        gap=torch.relu(.01-cone);loss=torch.mean(gap*gap);loss.backward()
        return float(loss.detach()),p.grad.detach().numpy().copy()
    rng=np.random.default_rng(4444)
    for j in range(args.restarts):
        start=time.time();th=np.zeros(28) if j==0 else rng.normal(0,.3+(.1*(j%4)),28)
        res=minimize(objective,th,jac=True,method='L-BFGS-B',bounds=[(-5,5)]*28,options={'maxiter':6000,'ftol':1e-15,'gtol':1e-10,'maxls':40})
        K=np.zeros((8,8));ix=np.triu_indices(8,1);K[ix]=res.x;K=K-K.T;O=torch.matrix_exp(torch.tensor(J@K,dtype=torch.float64)).numpy();w=v@O@O0@Rinv
        margin=float(np.min(w[:,:4]-abs(w[:,4:])))
        rec={'restart':j,'loss':float(res.fun),'margin':margin,'iterations':res.nit,'seconds':time.time()-start,'V':w.tolist(),'H':H.tolist(),'constant':emb['theta'][-1],'isometry_parameters':res.x.tolist()}
        with Path(args.out).open('a') as f:f.write(json.dumps(rec)+'\n')
        print({k:v for k,v in rec.items() if k not in ['V','H','isometry_parameters']},flush=True)
        if margin>0:
            print('PURE-CONE PROJECTED RELAXATION FOUND. SELECTOR LIFT STILL REQUIRED.',flush=True);break


if __name__=='__main__':main()
