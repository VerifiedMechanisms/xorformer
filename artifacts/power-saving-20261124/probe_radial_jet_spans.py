#!/usr/bin/env python3
"""Finite-field rank experiment for radial numerator jets. Not a proof over R."""
import argparse, json, time
import numpy as np

PRIME=65521

def rref(a):
    a=np.array(a,dtype=np.int64,copy=True)%PRIME
    nr,nc=a.shape
    piv=[]
    rr=0
    for j in range(nc):
        z=np.flatnonzero(a[rr:,j])
        if len(z)==0: continue
        k=rr+int(z[0])
        if k!=rr: a[[rr,k]]=a[[k,rr]]
        a[rr]=(a[rr]*pow(int(a[rr,j]),-1,PRIME))%PRIME
        coeff=a[:,j].copy(); coeff[rr]=0
        a=(a-coeff[:,None]*a[rr][None,:])%PRIME
        piv.append(j); rr+=1
        if rr==nr: break
    return a,piv

def kernel(a):
    red,piv=rref(a)
    frees=[i for i in range(a.shape[1]) if i not in set(piv)]
    k=np.zeros((a.shape[1],len(frees)),dtype=np.int64)
    if frees:
        k[frees,np.arange(len(frees))]=1
        k[piv,:]=-red[:len(piv),frees]%PRIME
    return k,piv

def rank_basis(a):
    _,piv=rref(a)
    return a[:,piv]

def moments(n,h,kmax,seed,mode):
    rng=np.random.default_rng(seed)
    x=((np.arange(1<<n)[:,None]>>np.arange(n))&1).astype(np.int64)
    c=rng.integers(1,100,size=(h,n),dtype=np.int64)
    if mode=='small_support': c[:,2:]=c[0,2:]
    if mode=='pencil':
        u=rng.integers(1,100,size=(1,n),dtype=np.int64)
        v=rng.integers(1,100,size=(1,n),dtype=np.int64)
        c=u+np.arange(h)[:,None]*v
    val=x@c.T%PRIME
    power=np.ones_like(val)
    mats=[]
    for k in range(kmax+1):
        a=(x[:,:,None]*power[:,None,:]).reshape(1<<n,n*h)%PRIME
        bias=np.ones((1<<n,1),dtype=np.int64) if k==0 else np.zeros((1<<n,1),dtype=np.int64)
        mats.append(np.column_stack((bias,a)))
        power=(-power*val)%PRIME
    return mats,c.tolist()

def jet_span(mats,r,aligned=False):
    nn,d=mats[0].shape
    p=(r+1)*d
    ker=np.eye(p,dtype=np.int64)
    span=np.empty((nn,0),dtype=np.int64)
    history=[]
    for k in range(len(mats)):
        block=np.concatenate([mats[k-j] if k>=j else np.zeros((nn,d),dtype=np.int64) for j in range(r+1)],axis=1)
        im=block@ker%PRIME
        sub,piv=kernel(im)
        basis=im[:,piv]
        span=rank_basis(np.column_stack((span,basis)))
        history.append({'order':k,'new_germs':len(piv),'leading_span':span.shape[1],'remaining_germs':sub.shape[1]})
        if (not aligned and span.shape[1]>=d) or sub.shape[1]==0 or (aligned and k>r and len(piv)>=min(d,nn)-1): break
        ker=ker@sub%PRIME
    return {'r':r,'span_dimension':span.shape[1],'ambient_column_bound':d,'max_leading_image':max(v['new_germs'] for v in history),'aligned_nonconstant_full':any(v['order']>r and v['new_germs']>=min(d,nn)-1 for v in history),'history':history}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--n',type=int,required=True); ap.add_argument('--heads',type=int,required=True); ap.add_argument('--rmax',type=int,default=8); ap.add_argument('--kmax',type=int,default=32); ap.add_argument('--seed',type=int,default=1); ap.add_argument('--aligned',action='store_true'); ap.add_argument('--mode',choices=['generic','small_support','pencil'],default='generic')
    a=ap.parse_args(); start=time.time()
    mats,c=moments(a.n,a.heads,a.kmax,a.seed,a.mode)
    out={'kind':'finite_field_rank_experiment_not_real_proof','prime':PRIME,'arguments':vars(a),'directions':c,'results':[]}
    for r in range(a.rmax+1):
        rec=jet_span(mats,r,a.aligned); out['results'].append(rec)
        if (a.aligned and rec['aligned_nonconstant_full']) or (not a.aligned and rec['span_dimension']>=min(1+a.n*a.heads,1<<a.n)): break
    out['seconds']=time.time()-start
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
