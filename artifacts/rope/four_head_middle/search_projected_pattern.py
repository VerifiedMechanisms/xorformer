"""Fit a relaxed pure projected quadratic to the cross-only local pattern.
The free constant is a relaxation; success is NOT a pure Boolean certificate.
Run this numerical exploration with heavy.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import time
import numpy as np
from scipy.optimize import minimize
import torch

torch.set_default_dtype(torch.float64);torch.set_num_threads(1)


def pattern():
    base=-np.ones(16);points=[base.copy()];ys=[-1.]
    for i in range(16):
        z=base.copy();z[i]=1;points.append(z);ys.append(1.)
    for i in range(8):
        for j in range(8):
            if i!=j:
                z=base.copy();z[i]=z[8+j]=1;points.append(z);ys.append(-1.)
    for j in range(8):
        others=[i for i in range(8) if i!=j]
        plus=others[:3] if j==0 else [0]+[i for i in others if i!=0][:2]
        v=np.array([1. if i in plus else -1. for i in range(8)])
        for sign in [-1,1]:
            for yj in [-1,1]:
                z=base.copy();z[8:]=sign*v;z[8+j]=yj;points.append(z);ys.append(-float(yj))
    assert len(points)==105
    return np.array(points),np.array(ys)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--seed-file',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--variable-middle',action='store_true');ap.add_argument('--restarts',type=int,default=24);ap.add_argument('--maxiter',type=int,default=8000);a=ap.parse_args()
    obj=json.loads(a.seed_file.read_text());mat=lambda v:np.array([[float(Fraction(t)) for t in r] for r in v])
    H=mat(obj['H_unscaled']);H=H/np.linalg.norm(H,2);ht=torch.tensor(H)
    z,y=pattern();zt=torch.tensor(z);yt=torch.tensor(y)
    V=np.r_[mat(obj['X_unscaled']),mat(obj['Y_unscaled'])];V/=np.max(V[:,:4])
    base=np.r_[np.log(V[:,:4]).ravel(),np.arctanh(V[:,4:]/V[:,:4]).ravel(),0.]
    if a.variable_middle:
        bt=np.array([float(Fraction(x)) for x in obj['B'][0]])/float(Fraction(obj['alpha']))
        st=np.array([float(Fraction(x)) for x in obj['S'][0]])/float(Fraction(obj['alpha']))
        kk=np.array([float(Fraction(x)) for x in obj['k'][0]])
        ell=np.array([float(Fraction(x)) for x in obj['ell'][0]])
        middle=np.r_[bt,np.log(st-np.abs(bt)),kk,ell,0.]
        base=np.r_[base,middle]
    rng=np.random.default_rng(428223)
    for j in range(a.restarts):
        theta=base.copy()
        if j>0:theta+=rng.normal(0,.2+min(3,j*.15),theta.shape)
        if j%4==3:
            theta[:129]=np.r_[rng.normal(0,.2,64),rng.normal(0,1,64),0.]
            if a.variable_middle:theta[129:]=middle+rng.normal(0,.5,17)
        def fg(p):
            v=torch.tensor(p,requires_grad=True);s=torch.exp(v[:64].reshape(16,4));b=s*torch.tanh(v[64:128].reshape(16,4));V=torch.cat([s,b],dim=1)
            hnow=ht
            if a.variable_middle:
                bt=v[129:133];st=torch.sqrt(bt*bt+1e-16)+torch.exp(v[133:137]);kk=v[137:141];ell=v[141:145];tt=v[145]
                At=bt.sum()-bt[:,None]-bt[None,:];At=At-torch.diag(torch.diag(At));ut=kk*st+ell*bt
                Lt=ut.sum()-ut[:,None]-ut[None,:]+(tt+ell[:,None]+ell[None,:])*At;Lt=Lt-torch.diag(torch.diag(Lt))
                KA=kk[:,None]*At;zero=torch.zeros((4,4));hnow=torch.cat([torch.cat([zero,KA],dim=1),torch.cat([KA.T,Lt],dim=1)],dim=0)
                hnow=hnow/torch.linalg.matrix_norm(hnow)
            W=zt@V;pred=v[128]+.5*torch.sum((W@hnow)*W,dim=1)
            gap=torch.relu(1-yt*pred);loss=torch.mean(gap**2)+1e-12*torch.sum(v*v)
            loss.backward();return loss.item(),v.grad.detach().numpy()
        start=time.time();r=minimize(fg,theta,jac=True,method='L-BFGS-B',bounds=[(-15,15)]*128+[(None,None)]+([(-30,30)]*4+[(-15,15)]*4+[(None,None)]*9 if a.variable_middle else []),options={'maxiter':a.maxiter,'ftol':1e-16,'gtol':1e-10,'maxls':40})
        p=r.x
        if a.variable_middle:
            bt=p[129:133];st=np.sqrt(bt*bt+1e-16)+np.exp(p[133:137]);kk=p[137:141];ell=p[141:145];tt=p[145]
            At=bt.sum()-bt[:,None]-bt[None,:];np.fill_diagonal(At,0);ut=kk*st+ell*bt
            Lt=ut.sum()-ut[:,None]-ut[None,:]+(tt+ell[:,None]+ell[None,:])*At;np.fill_diagonal(Lt,0);KA=kk[:,None]*At
            H=np.block([[np.zeros((4,4)),KA],[KA.T,Lt]]);H/=np.linalg.norm(H)
        S=np.exp(p[:64].reshape(16,4));B=S*np.tanh(p[64:128].reshape(16,4));V=np.c_[S,B];G=V@H@V.T;pred=p[128]+.5*np.einsum('ni,ij,nj->n',z,G,z);C=G[:8,8:]
        result={'status':'relaxed projected quadratic only; no Boolean certificate','restart':j,'loss':float(r.fun),'iterations':r.nit,'seconds':time.time()-start,'minimum_margin':float(np.min(y*pred)),'errors':int(np.sum(y*pred<=0)),'V':V.tolist(),'H':H.tolist(),'constant':float(p[128]),'C':C.tolist(),'theta':p.tolist()}
        with a.out.open('a') as f:f.write(json.dumps(result)+'\n')
        print({k:v for k,v in result.items() if k not in ['V','H','C','theta']},flush=True)
        if result['minimum_margin']>0:
            print('RELAXED PROJECTION FOUND; ORIGINAL PURE SCORE STILL REQUIRED.',flush=True);break

if __name__=='__main__':main()
