#!/usr/bin/env python3
"""Exact full-cube checks, both on denominator faces and after admissible perturbation."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path


def check(cert,labels,n,scale,perturb):
    def rounded(v): return F(round(v*scale),scale)
    w=[[rounded(v) for v in row] for row in cert['boundary_weights']]
    a=[[rounded(v) for v in row] for row in cert['numerators']]
    b=rounded(cert['bias'])
    assert all(row[0]>0 and all(v>=0 for v in row[1:]) for row in w)
    if perturb:
        w=[[v+F(1,scale) if j>0 else v for j,v in enumerate(row)] for row in w]
        assert all(v>0 for row in w for v in row)
    cols=[]
    for h,row in enumerate(w):
        col=[]
        for k in range(2**n):
            x=[(k>>i)&1 for i in range(n)]
            u=x if cert['orientation'][h]>0 else [1-t for t in x]
            den=row[0]+sum(row[i+1]*u[i] for i in range(n))
            num=a[h][0]+sum(a[h][i+1]*x[i] for i in range(n))
            assert den>0
            col.append(num/den)
        cols.append(col)
    centers=[(min(col)+max(col))/2 for col in cols]
    amplitude=abs(b+sum(centers))+sum((max(col)-min(col))/2 for col in cols)
    gap=min((1 if sign=='+' else -1)*(b+sum(col[k] for col in cols))
            for k,sign in enumerate(labels))
    assert gap>0 and amplitude>0
    margin=gap/amplitude
    return {'strict_rows':2**n,'head_count':len(cols),
            'margin_lower_millionths':margin.numerator*10**6//margin.denominator,
            'active_boundary_slopes':[sum(v>0 for v in row[1:]) for row in w]}


p=argparse.ArgumentParser();p.add_argument('inputs',nargs='+');p.add_argument('--output',required=True)
p.add_argument('--scale',type=int,default=10**10);args=p.parse_args();reports=[]
for path in args.inputs:
    d=json.loads(Path(path).read_text());checks=[];unresolved=[]
    for row in d['results']:
        if row['best']['checked_margin']<=1e-7:
            unresolved.append(row['index']);continue
        checks.append({'index':row['index'],
                       'boundary':check(row['best'],row['labels'],d['n'],args.scale,False),
                       'genuine_positive_slopes':check(row['best'],row['labels'],d['n'],args.scale,True)})
    reports.append({'input':path,'verified':len(checks),'unresolved_numerical_indices':unresolved,
                    'checks':checks})
Path(args.output).write_text(json.dumps({'status':'exact finite rational computation, not Lean proof',
                                       'rounding_denominator':args.scale,'reports':reports},indent=2)+'\n')
print(json.dumps([{'input':r['input'],'verified':r['verified'],
                   'unresolved':r['unresolved_numerical_indices']} for r in reports],indent=2))
