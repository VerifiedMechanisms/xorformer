"""Exact dual audit of the mixed binary fiber. Run through heavy.
The retained example is not a numerator-norm minimum: its unique signed dual
has negative coordinates, and a full-cube unit-margin constraint fails.
"""
import sys,json,time
from pathlib import Path
from fractions import Fraction as Q
from math import prod
sys.path.insert(0,str(Path(__file__).resolve().parent))
from verify_zero_fiber_dual import solve_exact
root=Path(__file__).resolve().parent
c=json.loads((root/'integer-binary-fiber-18.json').read_text());d=json.loads((root/'integer-binary-fiber-matrices.json').read_text())
n=c['n'];h=c['heads'];u=c['numerator_scaled_slopes'];b=c['denominator_slopes'];scale=c['numerator_scale'];M=d['cleared_jacobian'];size=len(M)
start=time.monotonic();w=solve_exact([list(x) for x in zip(*M)],[2*v for row in u for v in row]+[0]*(n*h))
scales=[]
for v in c['sample_indices']:
 den=[1+sum(row[i]*((v>>i)&1) for i in range(n)) for row in b]
 scales.append(scale*prod(x*x for x in den))
v=[Q(scales[i],scale)*w[i] for i in range(size)]
labels=c['labels'];signed=[labels[i]*v[i] for i in range(size)]
assert all(sum(Q(M[i][j],scales[i])*v[i] for i in range(size))==Q(([2*a for row in u for a in row]+[0]*(n*h))[j],scale) for j in range(size))
violating=None
for vertex in range(1,2**n):
 den=[1+sum(row[i]*((vertex>>i)&1) for i in range(n)) for row in b]
 num=[sum(row[i]*((vertex>>i)&1) for i in range(n)) for row in u]
 value=1+sum(Q(num[k],scale*den[k]) for k in range(h))
 if abs(value)<1:violating=dict(vertex=vertex,score=str(value));break
r=dict(status='PASS',signed_dual=[str(x) for x in signed],positive=sum(x>0 for x in signed),negative=sum(x<0 for x in signed),zero=sum(x==0 for x in signed),unit_margin_violation=violating,elapsed_seconds=time.monotonic()-start,main_target_proved=False)
(root/'integer-binary-dual-checks.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='signed_dual'}),flush=True)
