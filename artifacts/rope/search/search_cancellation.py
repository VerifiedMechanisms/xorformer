"""Bias the two-head search toward scores with weak degree-zero/one Fourier terms."""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.linalg import eigh
from search_two_head import vertices,fit_vanilla


def generate(Z,rng,n):
    a=rng.integers(1,100,(2,n)); b=rng.integers(1,100,(2,n)); gamma=rng.integers(1,100,2)
    if rng.random()<.5:
        a[1]=np.maximum(1,a[0]+rng.integers(-30,31,n))
        b[1]=np.maximum(1,b[0]+rng.integers(-30,31,n))
    X=((Z+1)/2).astype(int); D=gamma+(1-X)@a.T+X@b.T
    F=np.column_stack([(X@b[h])/D[:,h] for h in range(2)]+[gamma[h]/D[:,h] for h in range(2)])
    means=F.mean(axis=0); F0=F-means
    L=Z.T@F0/len(Z); G=F0.T@F0/len(Z)
    _,vec=eigh(L.T@L,G+1e-14*np.eye(4))
    coef=vec[:,0]; coef/=np.max(abs(coef)); coef=np.rint(coef*100000).astype(int)
    values=np.column_stack([np.zeros(2,dtype=int),coef[:2],coef[2:]])
    N=gamma*values[:,2]+X@(b*values[:,1,None]).T
    cnum=-int(round(float(means@coef)*2))+1; cden=2
    P=cnum*D[:,0]*D[:,1]+cden*(N[:,0]*D[:,1]+N[:,1]*D[:,0])
    if np.any(P==0): return generate(Z,rng,n)
    y=np.sign(P)
    return y,{'a':a.tolist(),'b':b.tolist(),'gamma':gamma.tolist(),'values':values.tolist(),'constant':[cnum,cden],'truth_table':hex(sum(int(v>0)<<i for i,v in enumerate(y))),'minimum_cleared_margin':int(np.min(abs(P)))}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--n',type=int,default=10);ap.add_argument('--samples',type=int,default=100);ap.add_argument('--restarts',type=int,default=10);ap.add_argument('--seed',type=int,default=771177);args=ap.parse_args()
    rng=np.random.default_rng(args.seed);Z=vertices(args.n)
    out=Path(f'artifacts/rope/search/cancellation_n{args.n}_{args.seed}.jsonl')
    for i in range(args.samples):
        y,cert=generate(Z,rng,args.n);t=time.time();fit=fit_vanilla(Z,y,args.restarts,rng)
        record={'sample':i,'n':args.n,'pure_certificate':cert,'vanilla_search':fit,'seconds':time.time()-t}
        with out.open('a') as f:f.write(json.dumps(record)+'\n')
        print(i,fit['status'],fit['restarts'],round(fit['loss'],8),round(record['seconds'],2),flush=True)

if __name__=='__main__':main()
