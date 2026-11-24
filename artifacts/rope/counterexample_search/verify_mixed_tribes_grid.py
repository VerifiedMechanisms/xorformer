"""Exact three-head certificates for six-group mixed tribes.

All coefficients are shared within groups, and every possible count tuple is
checked. Thus checking (m+1)^6 count tuples covers all 2^(6m) Boolean inputs.
"""
import argparse
import itertools
import json
from pathlib import Path


def verify(record):
    m=record['m'];cert=record['vanilla_certificate']
    ds=cert['denominators'];ns=cert['numerators']
    assert len(ds)==len(ns)==3
    for d in ds:
        assert len(d)==7 and d[0]>m*sum(abs(v) for v in d[1:])
        assert all(v>0 for v in d[1:]) or all(v<0 for v in d[1:])
    minimum=None
    for counts in itertools.product(range(m+1),repeat=6):
        z=[1]+[2*c-m for c in counts]
        positive=any(counts[2*h]==m and counts[2*h+1]==0 for h in range(3))
        label=1 if positive else -1
        d=[sum(a*b for a,b in zip(row,z)) for row in ds]
        n=[sum(a*b for a,b in zip(row,z)) for row in ns]
        value=sum(n[h]*d[(h+1)%3]*d[(h+2)%3] for h in range(3))
        assert label*value>0,(counts,value)
        minimum=abs(value) if minimum is None else min(minimum,abs(value))
        # The pure score is sum_h 1/(1/10+distance_h)-5.
        pd=[1+10*(m-counts[2*h]+counts[2*h+1]) for h in range(3)]
        pp=-5*pd[0]*pd[1]*pd[2]+10*sum(pd[(h+1)%3]*pd[(h+2)%3] for h in range(3))
        assert label*pp>0
    return minimum


def verify_degree_three():
    # After averaging a degree-two polynomial over literals within each term
    # and over the three terms, these four symmetric features span it.
    def features(w):
        a,b,c=w
        return [1,a+b+c,a*a+b*b+c*c,a*b+a*c+b*c]
    false_point=[0,3,3];true_point=[1,1,4]
    assert max(false_point)<4 and max(true_point)==4
    assert features(false_point)==features(true_point)==[1,6,18,9]


def rationalize(floating):
    import numpy as np
    from scipy.optimize import linprog
    from search_mixed_tribes_grid import data
    m=floating['m'];z,y=data(m);x=np.column_stack([np.ones(len(z)),z])
    for q in [10**4,10**6,10**9,10**12]:
        dens=[]
        for row in floating['beta']:
            slopes=[(1 if v>0 else -1)*max(1,round(abs(v)*q)) for v in row]
            gap=max(1,round((1-sum(abs(v) for v in row))*q))
            dens.append([sum(abs(v) for v in slopes)+gap]+slopes)
        d=x@np.array(dens).T/q
        f=np.column_stack([x*d[:,1,None]*d[:,2,None],x*d[:,0,None]*d[:,2,None],x*d[:,0,None]*d[:,1,None]])
        lp=linprog(np.zeros(21),A_ub=-y[:,None]*f,b_ub=-np.ones(len(y)),bounds=[(None,None)]*21,method='highs')
        if not lp.success:continue
        for scale in [10**4,10**6,10**9,10**12]:
            nums=[[round(v*scale) for v in row] for row in lp.x.reshape(3,7)]
            # z in the floating fit is the centered count divided by m.
            # Multiply numerator and denominator constants by m to remove it.
            intdens=[[m*row[0]]+row[1:] for row in dens]
            intnums=[[m*row[0]]+row[1:] for row in nums]
            record={'m':m,'vanilla_certificate':{'denominators':intdens,'numerators':intnums}}
            try:record['minimum_cleared_margin']=verify(record)
            except AssertionError:continue
            return record
    raise ValueError('failed rationalization')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('files',nargs='+');ap.add_argument('--out')
    args=ap.parse_args();records=[]
    verify_degree_three()
    for path in args.files:
        for line in Path(path).read_text().splitlines():
            r=json.loads(line)
            if args.out:
                if not r['success']:continue
                r=rationalize(r)
            margin=verify(r);records.append(r)
            print('exact six-group tribes','m',r['m'],'bits',6*r['m'],'count tuples',(r['m']+1)**6,'margin',margin)
    if args.out:
        Path(args.out).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in records))


if __name__=='__main__':main()
