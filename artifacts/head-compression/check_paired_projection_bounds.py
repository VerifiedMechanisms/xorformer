#!/usr/bin/env python3
"""Exact finite diagnostics for the manual paired-projection theorem.

These checks test the quotient maps, stopping bounds, and forest encoding.
They are not a proof of the general theorem or of the head conjecture.
"""
import argparse
from collections import deque
import json
from pathlib import Path
import random
import time


def projections(p, i, flipped):
    return (p[0]+p[i] if flipped else p[0],
            *(p[j] for j in range(1,len(p)) if j != i))


def check(states, rules):
    n=len(states[0])-1; M=len(states)
    terminal=set(range(M))-set(rules); L=len(terminal)
    assert L
    assert len({p[1:] for p in states}) <= L
    plus=[];minus=[]
    for i in range(1,n+1):
        a=sum(flips[i-1] for _,flips,_ in rules.values())
        p=len({projections(v,i,False) for v in states})
        m=len({projections(v,i,True) for v in states})
        assert p <= L+a and m <= M-a,(n,M,L,i,p,m,a)
        plus.append(p);minus.append(m)
    assert (2*M)**n <= L*(M+L)**n,(n,M,L)
    if L<2**n:
        assert (2**n-L)*M <= (2**n-1)*L*L
    # Reconstruct every state from one root vector and signed tree lengths.
    adjacency=[[] for _ in states]
    for v,(children,flips,delta) in rules.items():
        directions=[(1,)+(0,)*n]
        for i,f in enumerate(flips,1):
            directions.append(tuple((1 if j==0 else -1 if j==i else 0) if f
                                    else int(j==i) for j in range(n+1)))
        for w,d in zip(children,directions):
            assert tuple(states[v][j]+delta*d[j] for j in range(n+1))==states[w]
            adjacency[v].append((w,d,delta));adjacency[w].append((v,d,-delta))
    recovered={0:states[0]}; todo=deque([0])
    while todo:
        v=todo.popleft()
        for w,d,t in adjacency[v]:
            if w not in recovered:
                recovered[w]=tuple(recovered[v][j]+t*d[j] for j in range(n+1))
                assert recovered[w]==states[w]
                todo.append(w)
    assert len(recovered)==M
    return {'n':n,'states':M,'terminals':L,'below_full_cube_threshold':L<2**n}


def random_graph(rng,n):
    states=[(rng.randint(2,5),*(rng.randint(2,6) for _ in range(n)))]; index={states[0]:0}
    rules={}; cursor=0; cap=rng.randint(n+2,180); max_height=rng.randint(3,20)
    initial=2*states[0][0]+sum(states[0][1:]); stop=rng.choice([0,.05,.2,.4])
    while cursor<len(states):
        v=cursor;cursor+=1;p=states[v]
        if len(states)+n+1>cap or 2*p[0]+sum(p[1:])>=initial+max_height or rng.random()<stop:
            continue
        flips=tuple(bool(rng.randrange(2)) and p[i]>1 for i in range(1,n+1))
        bound=min([3,*[p[i]-1 for i,f in enumerate(flips,1) if f]])
        delta=rng.randint(1,bound);children=[]
        for i in range(n+1):
            q=list(p)
            if i==0:q[0]+=delta
            elif flips[i-1]:q[0]+=delta;q[i]-=delta
            else:q[i]+=delta
            q=tuple(q)
            if q not in index:index[q]=len(states);states.append(q)
            children.append(index[q])
        rules[v]=(children,flips,delta)
    return states,rules


def ladder(n,m):
    from itertools import product
    zs=list(product((0,1),repeat=n));states=[(2+k,*(3+z for z in bits)) for k in range(m+1) for bits in zs]
    idx={p:i for i,p in enumerate(states)};rules={}
    for v,p in enumerate(states):
        if p[0]==2+m:continue
        children=[idx[(p[0]+1,*p[1:])]];flips=tuple(z==4 for z in p[1:])
        for i,f in enumerate(flips,1):
            q=list(p)
            if f:q[0]+=1;q[i]-=1
            else:q[i]+=1
            children.append(idx[tuple(q)])
        rules[v]=(children,flips,1)
    return states,rules


def main(args):
    start=time.monotonic();rng=random.Random(2026112320);below=0;largest=0
    for _ in range(args.trials):
        s,r=random_graph(rng,rng.randint(1,7));x=check(s,r)
        below+=x['below_full_cube_threshold'];largest=max(largest,x['states'])
    ladders=[]
    for n in range(1,7):
        for m in (1,2,4,9):
            s,r=ladder(n,m);x=check(s,r)
            assert len(s)==(m+1)*2**n and x['terminals']==2**n
            if m>=2:assert len(s)>2*x['terminals']
            ladders.append(x|{'ladder_length':m})
    report={'random_graphs':args.trials,'seed':2026112320,'below_full_cube_threshold':below,
            'largest_random_state_count':largest,'ladder_cases':ladders,
            'exact_integer_checks_passed':True,'seconds':time.monotonic()-start,
            'scope':'Finite diagnostics only. The general inequalities are manual proofs; the universal head upper bound remains unproved.',
            'target_proved':False}
    args.out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='ladder_cases'}))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--trials',type=int,default=2000)
    p.add_argument('--out',type=Path,required=True);main(p.parse_args())
