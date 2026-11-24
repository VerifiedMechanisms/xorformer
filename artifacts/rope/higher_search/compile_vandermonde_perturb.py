"""Construct and exactly check oriented denominators for perturbed cubic samples.

A common translation and positive rescaling of all three denominator directions
preserves the baseline Vandermonde signs. A floating LP proposes numerators for
perturbed labels; integer arithmetic alone decides whether the proposal works.
Failure does not establish any lower bound. Run large batches with heavy.
"""
import argparse
from fractions import Fraction as Q
from math import lcm
import json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


def compile_record(rec):
    n=rec['n']; obj=rec['pure_certificate']; atoms=obj['atoms']
    betas=[]
    for a in atoms:
        av=list(map(lambda z:Q(*z),a['a'])); bv=list(map(lambda z:Q(*z),a['b']))
        center=Q(*a['gamma'])+sum((u+v)/2 for u,v in zip(av,bv))
        betas.append([(v-u)/(2*center) for u,v in zip(av,bv)])
    z=np.array([[2*((v>>i)&1)-1 for i in range(n)] for v in range(1<<n)],dtype=int)
    truth=int(obj['truth_table'],16); y=np.array([1 if (truth>>v)&1 else -1 for v in range(1<<n)])
    x=np.column_stack([np.ones(len(z)),z])
    for delta in [Q(1,10000),Q(1,100),Q(1,10),Q(1)]:
        common=[delta-min(b[i] for b in betas) for i in range(n)]
        positive=[[b[i]+common[i] for i in range(n)] for b in betas]
        scale=Q(4,5)/max(map(sum,positive))
        bq=[[scale*v for v in row] for row in positive]
        b=np.array(bq,dtype=float); d=1+z@b.T
        f=np.column_stack([x*(d[:,(h+1)%3]*d[:,(h+2)%3])[:,None] for h in range(3)])
        lp=linprog(np.zeros(3*(n+1)),A_ub=-y[:,None]*f,b_ub=-np.ones(len(y)),bounds=[(None,None)]*(3*(n+1)),method='highs')
        if not lp.success: continue
        dd=[]
        for row in bq:
            common_den=lcm(*(v.denominator for v in row)); dd.append([common_den]+[int(v*common_den) for v in row])
        for digits in [6,9,12]:
            nn=[[int(round(v*10**digits)) for v in row] for row in lp.x.reshape(3,n+1)]
            # The LP used normalized denominators; rescale numerators to integer D.
            nn=[[v*dd[h][0] for v in row] for h,row in enumerate(nn)]
            margin=None
            for v in range(1<<n):
                zz=[int(t) for t in z[v]]
                ds=[row[0]+sum(a*t for a,t in zip(row[1:],zz)) for row in dd]
                ns=[row[0]+sum(a*t for a,t in zip(row[1:],zz)) for row in nn]
                assert all(t>0 for t in ds)
                p=sum(ns[h]*ds[(h+1)%3]*ds[(h+2)%3] for h in range(3))*int(y[v])
                margin=p if margin is None else min(margin,p)
                if p<=0:break
            if margin>0:
                return {'n':n,'sample':rec['sample'],'truth_table':obj['truth_table'],'denominators':dd,'numerators':nn,'minimum_integer_cleared_margin':margin,'baseline_zero_vertices':obj['baseline_zero_vertices']}
    return None


def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    ok=0;total=0;zero=0
    for line in args.input.read_text().splitlines():
        rec=json.loads(line); total+=1; out=compile_record(rec)
        if out:
            ok+=1;zero+=out['baseline_zero_vertices']>0
            with args.out.open('a') as f:f.write(json.dumps(out)+'\n')
        print(rec['sample'],'exact vanilla3' if out else 'unresolved',flush=True)
    print({'total':total,'exact_vanilla_three':ok,'perturbed_zero_set_certificates':zero})

if __name__=='__main__':main()
