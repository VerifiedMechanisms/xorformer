"""Check an exact split-quadratic relaxation of the middle witness pattern.

This is deliberately not a pure-head certificate. The common positive column
avoids the earlier Gram obstruction, but the pure selector lift remains open.
Only standard-library arithmetic is used by verification.
"""
import argparse,json,math
from pathlib import Path


def points():
    base=[-1]*16
    yield base,-1
    for i in range(16):
        z=base.copy();z[i]=1;yield z,1
    for i in range(8):
        for j in range(8):
            if i!=j:
                z=base.copy();z[2*i]=z[2*j+1]=1;yield z,-1
    for j in range(8):
        plus={1,2,3} if j==0 else {0,*[k for k in range(1,8) if k!=j][:2]}
        for orientation in [-1,1]:
            for value in [-1,1]:
                z=base.copy()
                for k in range(8):z[2*k+1]=orientation*(1 if k in plus else -1)
                z[2*j+1]=value;yield z,-value


def verify(rec):
    V=rec['V_integer'];constant=rec['constant_integer'];signs=[1]*4+[-1]*4
    assert len(V)==16 and all(len(row)==8 for row in V)
    assert all(row[0]>0 for row in V)
    gram=[[sum(signs[k]*V[i][k]*V[j][k] for k in range(8)) for j in range(16)] for i in range(16)]
    witnesses=list(points());margins=[]
    for z,y in witnesses:
        q=constant+sum(2*gram[i][j]*z[i]*z[j] for i in range(16) for j in range(i+1,16))
        assert y*q>0
        margins.append(y*q)
    cross=[[2*gram[2*i][2*j+1] for j in range(8)] for i in range(8)]
    assert all(cross[i][j]<0 for i in range(8) for j in range(8) if i!=j)
    assert all(sum(cross[i][j] for i in range(8))>0 for j in range(8))
    spatial={tuple(z) for z,_ in witnesses}
    assert len(witnesses)==105 and len(spatial)==91
    return {'distinct_spatial_witnesses':len(spatial),'distinct_selector_orbit_inputs':4*len(spatial),'minimum_integer_margin':min(margins),'common_positive_column':0,'status':'projected relaxation only; no pure architecture claim'}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('file');ap.add_argument('--rationalize',action='store_true');ap.add_argument('--out');args=ap.parse_args()
    rec=json.loads(Path(args.file).read_text())
    if args.rationalize:
        theta=rec['theta'];scale=10**6
        rows=[theta[8*i:8*i+8] for i in range(16)]
        for row in rows:row[0]=math.exp(row[0])
        rec={'status':'split quadratic and positive-functional relaxation only, not pure-head parameters','scale':scale,'V_integer':[[round(scale*v) for v in row] for row in rows],'constant_integer':round(scale*scale*theta[-1])}
        result=verify(rec);rec['verification']=result
        assert args.out
        Path(args.out).write_text(json.dumps(rec,indent=2)+'\n')
    else:result=verify(rec)
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':main()
