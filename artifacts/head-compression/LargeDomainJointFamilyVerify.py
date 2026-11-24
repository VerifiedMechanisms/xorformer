#!/usr/bin/env python3
"""Independently verify finite joint-family certificates with rational arithmetic.

No numpy, scipy, torch, optimization, or tolerance is used here. The data
specifies auxiliary paired row scores. Their two denominator families are
liftable to the full Boolean cube using the recorded embedding intercept;
this verifies the exact positive slack there and exact axis cancellation.
A separate column-bias head and global cover transfer remain necessary.
"""
import argparse, itertools, json
from fractions import Fraction as Q


def verify(data):
    args=data['args'];k=args['dimension'];H=args['heads'];s=args['columns']
    paired=args.get('paired',False);affine=args.get('affine_row',False)
    points=list(itertools.product((0,1),repeat=k))
    checked=[]
    for record in data['records']:
        cert=record.get('certificate')
        if cert is None:continue
        d=[[Q(x) for x in row] for row in cert['directions']]
        b=[[Q(x) for x in row] for row in cert['offsets']]
        c=[Q(x) for x in cert['coefficients']]
        baseline=Q(cert.get('baseline',str(args.get('baseline',1))))
        embedding=Q(cert.get('embedding_intercept',str(max(1+args['delta'],float(baseline))+args['delta'])))
        delta=Q(str(args['delta']))
        assert len(d)==H and all(len(row)==k for row in d)
        assert len(b)==H and all(len(row)==s for row in b)
        assert len(c)==s+H*s+(H*k if affine else 0)
        assert all(z>0 for row in d for z in row)
        assert all(1<=z<=1+delta for row in b for z in row)
        assert baseline>0
        if paired:
            # First full-cube denominator: embedding + d.x
            #   - sum_j (embedding-b_hj) w_j.
            # Second: embedding + d.x
            #   - sum_j (embedding-baseline) w_j.
            # Complementing every row bit gives strict reverse row slopes.
            assert embedding>baseline
            assert all(embedding>z for row in b for z in row)
            assert embedding-s*(embedding-baseline)>0
            assert all(embedding-sum(embedding-z for z in row)>0 for row in b)
            # At w=0 the denominators are identical, while the numerators
            # are A_h(x) and -A_h(x), hence exact pairwise cancellation.
        labels=record['labels']
        assert len(labels)==len(points) and all(len(row)==s for row in labels)
        margin=None
        for ix,x in enumerate(points):
            for j in range(s):
                val=c[j]
                for h in range(H):
                    rownum=sum(c[s+H*s+h*k+i]*x[i] for i in range(k)) if affine else Q(0)
                    den=b[h][j]+sum(d[h][i]*x[i] for i in range(k))
                    val+=(rownum+c[s+h*s+j])/den
                    if paired:
                        val-=rownum/(baseline+sum(d[h][i]*x[i] for i in range(k)))
                assert labels[ix][j] in (-1,1)
                signed=labels[ix][j]*val
                assert signed>0,(record['target'],ix,j,signed)
                margin=signed if margin is None else min(margin,signed)
        assert margin==Q(cert['exact_min_margin'])
        checked.append({'target':record['target'],'strict_signs':len(points)*s,
                        'exact_min_margin':str(margin)})
    return {'dimension':k,'columns':s,'heads_before_pairing':H,
            'paired':paired,'certified_families':len(checked),'recorded_families':len(data['records']),
            'checked':checked}


def main():
    p=argparse.ArgumentParser();p.add_argument('files',nargs='+');args=p.parse_args()
    for file in args.files:
        with open(file) as f:report=verify(json.load(f))
        print(json.dumps({'file':file,**report}))

if __name__=='__main__':main()
