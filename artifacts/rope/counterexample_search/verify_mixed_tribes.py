"""Independently check exact pure and vanilla three-head tribes certificates."""
import argparse
import json
from pathlib import Path


def pure_certificate(size):
    n=3*size;unit=10*(n+1)
    a=[];b=[]
    pattern=[1]*(size//2)+[0]*(size-size//2)
    for h in range(3):
        aa=[1]*n;bb=[1]*n
        for j,bit in enumerate(pattern):
            if bit:
                aa[h*size+j]+=unit
            else:
                bb[h*size+j]+=unit
        a.append(aa);b.append(bb)
    return {'a':a,'b':b,'gamma':[1]*3,'values':[[0,0,unit]]*3,'constant':[-5,1]}


def target(bits,size):
    pattern=[1]*(size//2)+[0]*(size-size//2)
    return any(bits[h*size:(h+1)*size]==pattern for h in range(3))


def verify(record):
    size=record['size'];n=3*size;p=record['pure_certificate']
    vd=record['vanilla_certificate']['denominators']
    vn=record['vanilla_certificate']['numerators']
    for d in vd:
        assert d[0]>sum(abs(v) for v in d[1:])
        assert all(v>0 for v in d[1:]) or all(v<0 for v in d[1:])
    minima=[None,None]
    for mask in range(1<<n):
        bits=[(mask>>j)&1 for j in range(n)];z=[1]+[2*x-1 for x in bits]
        pd=[p['gamma'][h]+sum(p['b'][h][j] if bits[j] else p['a'][h][j] for j in range(n)) for h in range(3)]
        pn=[p['gamma'][h]*p['values'][h][2] for h in range(3)]
        pure=-5*pd[0]*pd[1]*pd[2]+sum(pn[h]*pd[(h+1)%3]*pd[(h+2)%3] for h in range(3))
        ds=[sum(a*b for a,b in zip(d,z)) for d in vd]
        ns=[sum(a*b for a,b in zip(a,z)) for a in vn]
        vanilla=sum(ns[h]*ds[(h+1)%3]*ds[(h+2)%3] for h in range(3))
        label=1 if target(bits,size) else -1
        assert label*pure>0 and label*vanilla>0,(mask,pure,vanilla)
        for h,v in enumerate([pure,vanilla]):
            minima[h]=abs(v) if minima[h] is None else min(minima[h],abs(v))
    return minima


def rationalize(floating):
    import numpy as np
    from scipy.optimize import linprog
    from search_mixed_tribes import data
    size=floating['size'];z,y=data(size);x=np.column_stack([np.ones(len(z)),z]);n=z.shape[1]
    for q in [10**4,10**6,10**9,10**12]:
        dens=[]
        for row in floating['beta']:
            slopes=[(1 if v>0 else -1)*max(1,round(abs(v)*q)) for v in row]
            gap=max(1,round((1-sum(abs(v) for v in row))*q))
            dens.append([sum(abs(v) for v in slopes)+gap]+slopes)
        d=x@np.array(dens).T/q
        f=np.column_stack([x*d[:,1,None]*d[:,2,None],x*d[:,0,None]*d[:,2,None],x*d[:,0,None]*d[:,1,None]])
        lp=linprog(np.zeros(3*(n+1)),A_ub=-y[:,None]*f,b_ub=-np.ones(len(y)),bounds=[(None,None)]*(3*(n+1)),method='highs')
        if not lp.success:continue
        for scale in [10**4,10**6,10**9,10**12]:
            nums=[[round(v*scale) for v in row] for row in lp.x.reshape(3,n+1)]
            record={'size':size,'pure_certificate':pure_certificate(size),'vanilla_certificate':{'denominators':dens,'numerators':nums}}
            try:record['minimum_cleared_margins']=verify(record)
            except AssertionError:continue
            return record
    raise ValueError('failed rationalization')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('files',nargs='+');ap.add_argument('--out')
    args=ap.parse_args()
    records=[]
    for path in args.files:
        for line in Path(path).read_text().splitlines():
            r=json.loads(line)
            if args.out:
                if not r['success']:continue
                r=rationalize(r)
            margin=verify(r);records.append(r)
            print('exact mixed tribes',r['size'],'bits',3*r['size'],'margins',margin)
    if args.out:
        Path(args.out).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in records))


if __name__=='__main__':main()
