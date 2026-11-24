"""Active-set continuation for larger mixed tribes; failures are inconclusive."""
import argparse,json,time
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from search_mixed_tribes import fit
from search_mixed_tribes_grid import data


def scores(z,rec):
    x=np.column_stack([np.ones(len(z)),z]);d=1+z@np.array(rec['beta']).T
    num=x@np.array(rec['numerators']).T
    return np.sum(num*np.column_stack([d[:,1]*d[:,2],d[:,0]*d[:,2],d[:,0]*d[:,1]]),axis=1)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--m',type=int,default=6);ap.add_argument('--initial',required=True);ap.add_argument('--rounds',type=int,default=30);ap.add_argument('--maxiter',type=int,default=10000);ap.add_argument('--out',default='/tmp/mixed_tribes_active.jsonl');args=ap.parse_args()
    z,y=data(args.m);rng=np.random.default_rng(606066)
    initial=json.loads(Path(args.initial).read_text().splitlines()[-1]);initial['numerators']=initial['numerators'] or initial['optimizer_numerators']
    initial_margin=y*scores(z,initial)
    # Start with coarse-grid corners/midpoints and the continuation's worst cases.
    coarse=np.all((abs(z)<1e-9)|(abs(z)==1),axis=1)
    active=set(np.where(coarse)[0]);active.update(np.argsort(initial_margin)[:500]);active.update(rng.choice(len(z),500,replace=False))
    start=time.time()
    for step in range(args.rounds):
        ix=np.array(sorted(active));rec=next(fit(z[ix],y[ix],1,606066+step,args.maxiter,initial,regularization=1e-20))
        rec['numerators']=rec['numerators'] or rec['optimizer_numerators']
        margin=y*scores(z,rec);bad=np.where(margin<=0)[0]
        rec.update({'m':args.m,'round':step,'active_count':len(ix),'full_errors':len(bad),'full_margin':float(min(margin)),'success':len(bad)==0,'elapsed':time.time()-start})
        with Path(args.out).open('a') as f:f.write(json.dumps(rec)+'\n')
        print({k:v for k,v in rec.items() if k not in ['beta','numerators','optimizer_numerators']},flush=True)
        if not len(bad):
            print('FULL GRID FLOATING SUCCESS. EXACT VERIFICATION REQUIRED.',flush=True);return
        new=set(np.argsort(margin)[:200]);new.update(rng.choice(bad,min(200,len(bad)),replace=False));new-=active
        if not new:
            print('No new violating constraints; continuation plateau is inconclusive.',flush=True);return
        active.update(new);initial=rec


if __name__=='__main__':main()
