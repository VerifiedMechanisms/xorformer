#!/usr/bin/env python3
"""Exact rational checks of rounded numerical original-head certificates.

This is finite Python Fraction arithmetic, not Lean kernel verification.
All positive coherent denominator coefficients and every Boolean row are checked.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path


def check(cert,labels,n,scale):
    def rounded(v):return Fraction(round(v*scale),scale)
    w=[[rounded(v) for v in row] for row in cert['weights']]
    a=[[rounded(v) for v in row] for row in cert['numerators']]
    b=rounded(cert['bias']);h=len(w)
    assert all(v>0 for row in w for v in row)
    columns=[[] for _ in range(h)]
    for index in range(2**n):
        x=[(index>>i)&1 for i in range(n)]
        for j in range(h):
            u=x if cert['orientation'][j]>0 else [1-v for v in x]
            den=w[j][0]+sum(w[j][i+1]*u[i] for i in range(n))
            num=a[j][0]+sum(a[j][i+1]*x[i] for i in range(n))
            assert den>0
            columns[j].append(num/den)
    centers=[(max(col)+min(col))/2 for col in columns]
    cb=b+sum(centers)
    radii=[(max(col)-min(col))/2 for col in columns]
    amplitude=abs(cb)+sum(radii)
    original_amplitude=abs(b)+sum(max(abs(v) for v in col) for col in columns)
    assert amplitude<=original_amplitude
    gaps=[]
    for index,label in enumerate(labels):
        score=b+sum(col[index] for col in columns)
        centered_score=cb+sum(columns[j][index]-centers[j] for j in range(h))
        assert score==centered_score
        gaps.append(score*(1 if label=='+' else -1))
    gap=min(gaps)
    assert gap>0 and amplitude>0
    margin=gap/amplitude
    floor_micro=margin.numerator*10**6//margin.denominator
    assert margin>=Fraction(floor_micro,10**6)
    return {'strict_rows':2**n,'head_count':h,'rounding_denominator':scale,
            'margin_lower_millionths':floor_micro,'margin_float':float(margin),
            'centered_head_norms':[float(r) for r in radii],
            'centered_amplitude_float':float(amplitude),
            'min_denominator_coefficient_float':float(min(v for row in w for v in row))}

p=argparse.ArgumentParser();p.add_argument('inputs',nargs='+');p.add_argument('--output',required=True)
p.add_argument('--scale',type=int,default=10**9);args=p.parse_args()
reports=[]
for name in args.inputs:
    data=json.loads(Path(name).read_text())
    if 'results' in data:
        n=data['config']['n']; rows=data['results']
    else:
        n=data['n'];rows=[{'index':data['source_index'],'labels':data['labels'],'best':data['best']}]
    checks=[{'index':r['index'],**check(r['best'],r['labels'],n,args.scale)} for r in rows]
    reports.append({'input':name,'certificates':len(checks),'checks':checks,
                    'minimum_margin_lower_millionths':min(r['margin_lower_millionths'] for r in checks)})
Path(args.output).write_text(json.dumps({'status':'finite exact rational verification, not kernel checked','reports':reports},indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['input','certificates','minimum_margin_lower_millionths']} for r in reports],indent=2))
