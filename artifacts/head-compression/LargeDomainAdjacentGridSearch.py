#!/usr/bin/env python3
"""Exploratory adjacent-grid auxiliary decoder search; run under heavy.

This does not implement the global compiler. LargeDomainGridSupport.tex and
its Lean companion prove that the unmodified gates fail the required lower
layer support. Floating optimizer failure is not an impossibility result.
"""
import argparse,itertools,json,time
import numpy as np
import torch
p=argparse.ArgumentParser();p.add_argument('--a',type=int,default=4);p.add_argument('--m',type=int,default=8);p.add_argument('--s',type=int,default=16);p.add_argument('--iterations',type=int,default=3000);p.add_argument('--seed',type=int,default=1);p.add_argument('--delta',type=float,default=.05);p.add_argument('--pole-scale',type=float,default=1.);p.add_argument('--resume');p.add_argument('--fixed-q',action='store_true');p.add_argument('--structured',action='store_true');p.add_argument('--output',default='/tmp/LargeDomainAdjacentGrid.npz');args=p.parse_args()
torch.set_num_threads(2);torch.set_default_dtype(torch.float64);rng=np.random.default_rng(args.seed)
a,m,s=args.a,args.m,args.s;G=m**a;H=(m+1)**a;R=2**a
u=np.array(list(itertools.product(range(m),repeat=a)));e=np.array(list(itertools.product(range(2),repeat=a)))
v=u[:,None,:]+e[None,:,:];powers=(m+1)**np.arange(a-1,-1,-1);indices=(v*powers).sum(axis=2)
beta=args.pole_scale*rng.uniform(.2,2.,(H,a));levels=(beta[indices]*(1-e)[None,:,:]).sum(axis=2)
y=rng.choice([-1.,1.],(G,a,s))
if args.structured:
 for j in range(s):
  for i in range(a): y[:,i,j]=1-2*((u@rng.integers(0,2,a)+i+j)%2)
ixt=torch.tensor(indices);lv=torch.tensor(levels);yt=torch.tensor(y)
q=torch.nn.Parameter(torch.tensor(rng.normal(size=(H,a))));c=torch.nn.Parameter(torch.tensor(rng.normal(size=(H,s))/np.sqrt(R)));z=torch.nn.Parameter(torch.tensor(rng.normal(size=(H,s))));bias=torch.nn.Parameter(torch.zeros((a,s)))

if args.resume:
 old=np.load(args.resume); q.data=torch.tensor(old['q']);c.data=torch.tensor(old['c']);bias.data=torch.tensor(old['bias']);bb=(old['b']-1)/args.delta;z.data=torch.tensor(np.log(bb/(1-bb)))
params=[c,z,bias]+([] if args.fixed_q else [q]);opt=torch.optim.Adam(params,lr=.03)
start=time.time();best=1e9
for it in range(args.iterations):
 opt.zero_grad();b=1+args.delta*torch.sigmoid(z);w=c[ixt]/(b[ixt]+lv[:,:,None])**2
 out=torch.einsum('grs,gri->gis',w,q[ixt])+bias[None,:,:]
 margin=out*yt;loss=torch.relu(1-margin).square().mean()
 # Parameters may grow, but this tiny initial penalty avoids meaningless runaway before a direction is found.
 loss.backward();opt.step()
 if it%1000==0 or it+1==args.iterations:
  with torch.no_grad():
   failures=int((margin<=0).sum());low=float(margin.min());mean=float(loss);best=min(best,failures)
  print(json.dumps({'iter':it,'a':a,'m':m,'s':s,'H':H,'G':G,'failures':failures,'best':best,'minmargin':low,'loss':mean,'seconds':time.time()-start}),flush=True)
  if failures==0:
   np.savez(args.output,q=q.detach().numpy(),c=c.detach().numpy(),b=b.detach().numpy(),bias=bias.detach().numpy(),beta=beta,y=y,args=json.dumps(vars(args)))
   break
np.savez(args.output+'.last.npz',q=q.detach().numpy(),c=c.detach().numpy(),b=(1+args.delta*torch.sigmoid(z)).detach().numpy(),bias=bias.detach().numpy(),beta=beta,y=y,args=json.dumps(vars(args)))
