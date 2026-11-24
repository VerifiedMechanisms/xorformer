"""Rationalize proposed vanilla fits and independently check both architectures.
The eight-vertex parity restriction additionally certifies exact head count3.
"""
import argparse
from fractions import Fraction as Q
import json
from pathlib import Path
import numpy as np
from scipy.optimize import linprog


from verify_small import verify

def compile(rec):
    n=rec['n'];truth=int(rec['truth_table'],16);fit=rec['vanilla_search']
    if fit['status']!='floating_fit':return None
    z=np.array([[2*((m>>i)&1)-1 for i in range(n)] for m in range(1<<n)],dtype=int);x=np.c_[np.ones(len(z)),z];y=np.array([1 if truth>>m&1 else -1 for m in range(1<<n)])
    for digits in [6,9,12,15]:
        scale=10**digits;dd=[]
        for row in fit['B']:
            sign=1 if sum(row)>0 else -1;v=[sign*max(1,int(round(abs(b)*scale))) for b in row];dd.append([max(scale,sum(abs(b) for b in v)+1)]+v)
        d=np.array([[row[0]+sum(int(a)*int(b) for a,b in zip(row[1:],zz)) for row in dd] for zz in z],dtype=float);d/=np.array([row[0] for row in dd])
        f=np.column_stack([x*(d[:,(h+1)%3]*d[:,(h+2)%3])[:,None] for h in range(3)])
        lp=linprog(np.zeros(3*(n+1)),A_ub=-y[:,None]*f,b_ub=-np.ones(len(y)),bounds=[(None,None)]*(3*(n+1)),method='highs')
        if not lp.success:continue
        for nd in [6,9,12]:
            nn=[[int(round(a*10**nd))*dd[h][0] for a in row] for h,row in enumerate(lp.x.reshape(3,n+1))]
            margin=None
            for mask,zz in enumerate(z):
                ds=[row[0]+sum(int(a)*int(b) for a,b in zip(row[1:],zz)) for row in dd];ns=[row[0]+sum(int(a)*int(b) for a,b in zip(row[1:],zz)) for row in nn]
                val=int(y[mask])*sum(ns[h]*ds[(h+1)%3]*ds[(h+2)%3] for h in range(3));margin=val if margin is None else min(margin,val)
                if val<=0:break
            if margin>0:
                result={k:v for k,v in rec.items() if k not in ['vanilla_search','quadratic_screen','NRA']};result['vanilla_certificate']={'denominators':dd,'numerators':nn,'minimum_integer_cleared_margin':margin};verify(result);return result
    return None


def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--out',type=Path);a=ap.parse_args();records=[json.loads(l) for l in a.input.read_text().splitlines()];ok=0
    for r in records:
        if a.out:
            result=compile(r)
            if result:
                with a.out.open('a') as f:f.write(json.dumps(result,separators=(',',':'))+'\n')
                ok+=1
        else:verify(r);ok+=1
    print({'records':len(records),'exact_verified_pairs':ok,'parity_three_restrictions':ok})

if __name__=='__main__':main()
