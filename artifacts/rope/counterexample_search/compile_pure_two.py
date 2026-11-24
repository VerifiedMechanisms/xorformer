"""Construct and check two vanilla heads for every strict rational pure pair.

The compiler uses exact Fraction arithmetic. Its output is an ordinary vanilla
certificate with positive denominators and uniformly signed nonzero slopes.
It does not fit, optimize, or search for the vanilla parameters.
"""
from fractions import Fraction as F
from math import ceil, gcd, lcm
from pathlib import Path
import argparse
import copy
import json

def pure_forms(p):
    """Return bit-coordinate affine numerators and denominators."""
    ds, ns = [], []
    for a, b, g, values in zip(p['a'], p['b'], p['gamma'], p['values']):
        v0, v1, vq = values
        ds.append([F(g + sum(a))] + [F(bi-ai) for ai,bi in zip(a,b)])
        ns.append([F(g*vq + v0*sum(a))] + [F(v1*bi-v0*ai) for ai,bi in zip(a,b)])
    return ns, ds


def eval_form(a, bits):
    return a[0] + sum(ai*xi for ai,xi in zip(a[1:],bits))


def compile_pair(p):
    """Return exact bit-coordinate numerator/denominator pairs and metadata."""
    p=copy.deepcopy(p)
    n=len(p['a'][0])
    ns,ds=pure_forms(p)
    constant=F(*p['constant'])
    perturb=F(0)
    chosen=next((h for h in range(2) if p['values'][h][0]!=p['values'][h][1]),None)
    if chosen is None:
        # The finite strict margin controls changing one token-one value.
        maxden=[d[0]+sum(max(F(0),a) for a in d[1:]) for d in ds]
        margin=None
        for mask in range(1<<n):
            bits=[(mask>>i)&1 for i in range(n)]
            dv=[eval_form(d,bits) for d in ds]
            nv=[eval_form(a,bits) for a in ns]
            cleared=constant*dv[0]*dv[1]+nv[0]*dv[1]+nv[1]*dv[0]
            assert cleared!=0, 'input classifier must already be strict'
            margin=abs(cleared) if margin is None else min(margin,abs(cleared))
        perturb=margin/(2*maxden[0]*maxden[1])
        p['values'][0][1]=F(p['values'][0][1])+perturb
        ns,ds=pure_forms(p)
        chosen=0
    if chosen:
        ns.reverse();ds.reverse();p['values'].reverse()
    v0,v1,vq=map(F,p['values'][0])
    low,high=min(v0,v1),max(v0,v1)
    if vq>low:
        sigma,tau=F(1),-low
    else:
        sigma,tau=F(-1),high
    b=[sigma*a+tau*d for a,d in zip(ns[0],ds[0])]
    assert b[0]+sum(min(F(0),a) for a in b[1:])>0
    assert all(a>0 for a in b[1:]) or all(a<0 for a in b[1:])
    a=[sigma*d for d in ds[1]]
    c=[u+(constant-sigma*tau)*d for u,d in zip(ns[1],ds[1])]
    d=ds[0]
    e=1+max(ceil(abs(di/bi)) for di,bi in zip(d[1:],b[1:]))
    other=[e*bi+di for bi,di in zip(b,d)]
    nums=[c,[ai-e*ci for ai,ci in zip(a,c)]]
    dens=[b,other]
    # Scale each numerator/denominator pair by the same positive integer.
    integer_nums=[];integer_dens=[]
    for num,den in zip(nums,dens):
        scale=lcm(*(v.denominator for v in num+den))
        integer_nums.append([int(v*scale) for v in num])
        integer_dens.append([int(v*scale) for v in den])
    return {'numerators':integer_nums,'denominators':integer_dens,
            'perturbation':str(perturb),'selected_head':chosen,'compiler_scale':e}


def verify(p,cert):
    """Check full-cube classifier agreement using integers/Fractions only."""
    ns,ds=pure_forms(p)
    constant=F(*p['constant'])
    n=len(ds[0])-1
    for d in cert['denominators']:
        assert d[0]+sum(min(0,a) for a in d[1:])>0
        assert all(a>0 for a in d[1:]) or all(a<0 for a in d[1:])
    margin=None
    for mask in range(1<<n):
        bits=[(mask>>i)&1 for i in range(n)]
        dv=[eval_form(d,bits) for d in ds]
        nv=[eval_form(a,bits) for a in ns]
        pure=constant*dv[0]*dv[1]+nv[0]*dv[1]+nv[1]*dv[0]
        vd=[eval_form(d,bits) for d in cert['denominators']]
        vn=[eval_form(a,bits) for a in cert['numerators']]
        value=vn[0]*vd[1]+vn[1]*vd[0]
        assert pure*value>0,(mask,pure,value)
        if 'truth_table' in p:
            label=1 if (int(p['truth_table'],16)>>mask)&1 else -1
            assert label*value>0
        margin=abs(value) if margin is None else min(margin,abs(value))
    return margin


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('files',nargs='+')
    ap.add_argument('--out')
    args=ap.parse_args()
    total=perturbed=vertices=0
    output=[]
    for path in args.files:
        for line in Path(path).read_text().splitlines():
            record=json.loads(line)
            cert=compile_pair(record['pure_certificate'])
            margin=verify(record['pure_certificate'],cert)
            total+=1;vertices+=1<<record['n'];perturbed+=cert['perturbation']!='0'
            if args.out:
                output.append({'n':record['n'],'sample':record['sample'],'pure_certificate':record['pure_certificate'],'compiled_vanilla':cert,'minimum_integer_margin':int(margin)})
        print(path,total,'verified',flush=True)
    if args.out:
        Path(args.out).write_text(''.join(json.dumps(r,separators=(',',':'))+'\n' for r in output))
    print(f'EXACT COMPILE VERIFIED: {total} classifiers, {vertices} cube vertices, {perturbed} finite perturbations.')


if __name__=='__main__':
    main()
