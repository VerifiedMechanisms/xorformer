"""Search cone embeddings for a projected quadratic only, not a classifier.

The scalar constant is independently free in this relaxation. A success still
needs a valid selector parameter lift and full, unprojected Boolean signs.
"""
import argparse,json,time
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
from search_local_pure_four import data


def objective(theta,z,y,H):
    s=np.exp(theta[:64].reshape(16,4))
    tanh=np.tanh(theta[64:128].reshape(16,4))
    v=np.column_stack([s,s*tanh])
    gram=v@H@v.T
    np.fill_diagonal(gram,0)
    score=theta[-1]+np.sum((z@gram)*z,axis=1)
    gap=np.minimum(y*score-1,0);gp=2*gap*y/len(y)
    gg=z.T@(gp[:,None]*z)
    np.fill_diagonal(gg,0)
    gv=2*gg@v@H
    gs=(gv[:,:4]+gv[:,4:]*tanh)*s
    gt=gv[:,4:]*s*(1-tanh*tanh)
    return np.mean(gap*gap),np.concatenate([gs.ravel(),gt.ravel(),[sum(gp)]])


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seed-file',default='artifacts/rope/four_head_middle/seed.json');ap.add_argument('--restarts',type=int,default=30);ap.add_argument('--maxiter',type=int,default=10000);ap.add_argument('--out',default='/tmp/projected_embedding.jsonl');ap.add_argument('--pattern',choices=['old','middle'],default='old');args=ap.parse_args()
    r=json.loads(Path(args.seed_file).read_text());mat=lambda key:np.array([[float(Fraction(x)) for x in row] for row in r[key]])
    H=mat('H_unscaled');H/=np.max(abs(H))
    order=[i for j in range(8) for i in [j+1,j+9]]
    s=mat('S')[order];b=mat('B')[order]
    s/=np.max(s);b/=np.max(mat('S')[order])
    base=np.concatenate([np.log(s).ravel(),np.arctanh(b/s).ravel(),[-1.]])
    z,y=data(args.pattern);z=z[3::4,:16];y=y[3::4];rng=np.random.default_rng(999174)
    for j in range(args.restarts):
        if j==0:theta=base.copy()
        elif j%3==0:theta=np.concatenate([rng.normal(-1,1,64),rng.normal(0,2,64),[-1.]])
        else:theta=base+rng.normal(0,.1*(1+j%7),129)
        start=time.time();res=minimize(objective,theta,args=(z,y,H),jac=True,method='L-BFGS-B',bounds=[(-12,12)]*64+[(-12,12)]*64+[(None,None)],options={'maxiter':args.maxiter,'ftol':1e-14,'gtol':1e-9,'maxls':40})
        rec={'restart':j,'pattern':args.pattern,'loss':float(res.fun),'iterations':res.nit,'seconds':time.time()-start,'theta':res.x.tolist(),'H':H.tolist()}
        with Path(args.out).open('a') as f:f.write(json.dumps(rec)+'\n')
        print({k:v for k,v in rec.items() if k not in ['theta','H']},flush=True)
        if res.fun<1e-12:
            print('PROJECTED RELAXATION FEASIBLE. NOT A BOOLEAN CERTIFICATE.',flush=True);break


if __name__=='__main__':main()
