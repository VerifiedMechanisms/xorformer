#!/usr/bin/env python3
"""Exact finite paired-offset decoder audits. Run searches with heavy.

No search result establishes a growing family of universal decoders.
The default only checks rational identities. --dual computes and verifies
an independently readable Farkas certificate for a specified finite target.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse, importlib.util, itertools, json, math, random, sys, time
sys.set_int_max_str_digits(0)
spec=importlib.util.spec_from_file_location('bf',str(Path(__file__).with_name('butterfly-rectangle-decoder-check.py')))
bf=importlib.util.module_from_spec(spec);spec.loader.exec_module(bf)

def geometry(d):
    eps=F(1,100); gamma=[eps**(2**j) for j in range(d)]
    poles=[sum((gamma[j] for j in range(d) if y&(1<<j)),F(0)) for y in range(1<<d)]
    return gamma,poles

def mask(h,k,g,kind):
    if h>>(k+1)!=g:return 0
    return (1-2*((h>>k)&1)) if kind=='haar' else int(((h>>k)&1)==0)

def reduced_rows(d,bits,kind='left'):
    H=1<<d; sw=bf.switches(d); pi=bf.permutation(d,bits); inv=[pi.index(y) for y in range(H)]
    gamma,poles=geometry(d); blocks=list(dict.fromkeys((k,g) for k,s,g in sw)); rows=[]; labels=[]
    for k,g in blocks:
        pos=[s for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==0]
        neg=[s for e,(l,s,b) in enumerate(sw) if (l,b)==(k,g) and bits[e]==1]
        if not pos or not neg:continue
        values={}
        for s in pos+neg:
            t=1-poles[s]; gg=gamma[k]
            a=[mask(inv[y],k,g,kind)*gg/((t-poles[y])*(t+gg-poles[y])) for y in range(H)]
            b=gg*sum((mask(inv[y],k,g,kind)*(1/(t-poles[y])+1/(t+gg-poles[y])) for y in range(H)),F(0))
            values[s]=a+[b]
        for a in pos:
            for b in neg:
                rows.append(tuple(x-y for x,y in zip(values[a],values[b])))
                labels.append([k,g,a,b])
    return rows,labels

def seed_bits(d,seed):
    H=1<<d; rr=random.Random(seed)
    return [0]*(H//2)+[rr.randrange(2) for _ in range(len(bf.switches(d))-H//2)]

def rational_point(problem,n):
    import ppl
    pt=problem.optimizing_point()
    return [F(int(pt.coefficient(ppl.Variable(j))),int(pt.divisor())) for j in range(n)]

def primal(rows,H):
    import ppl
    cs=ppl.Constraint_System()
    for row in rows:
        den=math.lcm(*(x.denominator for x in row))
        cs.insert(ppl.Linear_Expression([int(x*den) for x in row],0)>=den)
    cs.insert(ppl.Variable(H)>=1)
    prob=ppl.MIP_Problem(H+1,cs,ppl.Linear_Expression(0))
    if not prob.is_satisfiable():return None
    point=rational_point(prob,H+1)
    assert point[-1]>=1
    assert all(sum(x*y for x,y in zip(row,point))>=1 for row in rows)
    return point

def dual(rows,H):
    import ppl
    n=len(rows); cs=ppl.Constraint_System()
    for i in range(n):cs.insert(ppl.Variable(i)>=0)
    cs.insert(ppl.Linear_Expression([1]*n,0)==1)
    for j in range(H+1):
        vals=[row[j] for row in rows]; den=math.lcm(*(v.denominator for v in vals))
        expr=ppl.Linear_Expression([int(v*den) for v in vals],0)
        cs.insert(expr==0 if j<H else expr<=0)
    prob=ppl.MIP_Problem(n,cs,ppl.Linear_Expression(0))
    if not prob.is_satisfiable():return None
    lam=rational_point(prob,n);verify_dual(rows,lam,H);return lam

def verify_dual(rows,lam,H):
    assert len(rows)==len(lam) and all(v>=0 for v in lam) and sum(lam)==1
    sums=[sum(lam[i]*rows[i][j] for i in range(len(rows))) for j in range(H+1)]
    assert all(v==0 for v in sums[:-1]) and sums[-1]<=0
    return sums[-1]

def identities():
    count=0
    for x,D,gg,kap,a in itertools.product(map(F,[0,1,2]),map(F,[5,7]),map(F,[1,2]),map(F,[-2,1,3]),map(F,[-1,0,4])):
        assert D>x+gg
        f=lambda p,b:(b+kap)/(D-p)-(b-kap)/(D+gg-p)
        assert f(x,kap)==f(x+gg,-kap)==2*kap/(D-x)
        assert f(x,a)==gg*a/((D-x)*(D+gg-x))+kap*(1/(D-x)+1/(D+gg-x))
        if kap==gg:
            assert f(x,a)==gg*(a+2*D+gg-2*x)/((D-x)*(D+gg-x))
        count+=1
    return count

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--d',type=int,default=3);ap.add_argument('--kind',choices=['left','haar'],default='left');ap.add_argument('--count',type=int,default=0);ap.add_argument('--seed',type=int,default=784);ap.add_argument('--dual',action='store_true');ap.add_argument('--verify');ap.add_argument('--save');args=ap.parse_args()
    print('rational identities',identities(),flush=True)
    if args.verify:
        data=json.loads(Path(args.verify).read_text());rows,labels=reduced_rows(data['d'],data['bits'],data['kind']);assert labels==data['labels']
        value=verify_dual(rows,list(map(F,data['lambda'])),1<<data['d'])
        print('verified Farkas certificate; support',sum(F(v)>0 for v in data['lambda']),'affine sign',0 if value==0 else -1);return
    if args.dual:
        bits=seed_bits(args.d,args.seed);rows,labels=reduced_rows(args.d,bits,args.kind);lam=dual(rows,1<<args.d)
        assert lam is not None,'no dual certificate'
        data=dict(d=args.d,kind=args.kind,bits=bits,labels=labels,**{'lambda':list(map(str,lam))})
        if args.save:Path(args.save).write_text(json.dumps(data,separators=(',',':'))+'\n')
        print('verified Farkas certificate; support',sum(v>0 for v in lam));return
    if args.count:
        H=1<<args.d;tail_len=len(bf.switches(args.d))-H//2;start=time.time();sat=0;witnesses=[];bad=[]
        targets=([0]*(H//2)+list(t) for t in itertools.product((0,1),repeat=tail_len)) if args.count<0 else (seed_bits(args.d,args.seed+t)for t in range(args.count))
        for count,bits in enumerate(targets,1):
            rows,_=reduced_rows(args.d,bits,args.kind);point=primal(rows,H)
            if point is None:bad.append(bits)
            else:sat+=1;witnesses.append(dict(bits=bits,point=list(map(str,point))))
            if args.save:Path(args.save).write_text(json.dumps(dict(d=args.d,kind=args.kind,total=count,sat=sat,bad=bad,witnesses=witnesses),separators=(',',':'))+'\n')
            if count%32==0 or args.d>3:print('targets',count,'feasible',sat,'seconds',round(time.time()-start,2),flush=True)
        print('finite total',count,'feasible',sat,'failed',len(bad),flush=True)
if __name__=='__main__':main()
