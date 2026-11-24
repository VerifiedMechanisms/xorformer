"""Exact arithmetic audit for the all-K equal-weight rounding obstruction.

The proof is in equal_weight_permutation_rounding_obstruction.md.
No floating point arithmetic and no Lean verification are used here.
"""
import itertools
import json
from pathlib import Path
import sympy as s

xs=list(itertools.product([0,1], repeat=3))
p=[1+x[0]+2*x[1]+4*x[2] for x in xs]
c1=s.Matrix([s.Rational(1,a+1) for a in p])
c2=s.Matrix([s.Rational(1,a+2) for a in p])
F=s.Matrix([[1,*x,c1[i],c2[i]] for i,x in enumerate(xs)])
Q=s.Matrix([[-143,1988,-2895,1050,1193,-3038,1845,0],
            [106,1001,399,-1506,-505,-602,0,1107]])
assert F.rank()==6 and Q.rank()==2 and Q*F==s.zeros(2,6)
D=s.Matrix([[(c1[i]-c2[i])*x[j] for j in range(3)] for i,x in enumerate(xs)])
R=Q*D
assert R==s.Matrix([[s.Rational(320,3),-s.Rational(206,3),s.Rational(23,3)],
                   [-s.Rational(608,15),s.Rational(34,3),s.Rational(67,15)]])
assert R[:,:2].det()==-s.Rational(7872,5)
u=s.Matrix([143,-106]); v=s.Matrix([-1050,1506])
det=lambda a,b:s.Matrix.hstack(a,b).det()
assert det(u,v)==104058
ys=[-1,1,-1,-1,1,-1,1,1]
gens=[ys[i]*Q[:,i] for i in range(8)]
assert all(det(u,w)>=0 and det(w,v)>=0 for w in gens)
assert gens[0]==u and gens[3]==v
assert all(sum(w)>0 for w in gens)
K=s.Symbol('K',integer=True,positive=True)
T=s.Matrix.hstack(u-v,-(K+1)*u+(K+2)*v)
assert T*s.Matrix([K+2,1])==u and T*s.Matrix([K+1,1])==v
assert s.simplify(T.det())==104058
B2=s.simplify(R[:,:2].inv()*T)
B=s.Matrix.vstack(B2,s.zeros(1,2))
assert s.simplify(R*B-T)==s.zeros(2,2)
slopes=[B[:,0],-B[:,0],B[:,1],-B[:,1]]
possible=set()
for pair in itertools.combinations(range(4),2):
    z=slopes[pair[0]]+slopes[pair[1]]
    coeff=s.simplify(T.inv()*R*z)
    possible.add(tuple(coeff))
assert possible=={(0,0),(1,1),(1,-1),(-1,1),(-1,-1)}
result={
  'scope':'Exact rational and symbolic checks supporting a written template obstruction; not an unrestricted head lower bound or Lean proof.',
  'p_values':p,'target':ys,'Q':Q.tolist(),'free_rank':F.rank(),
  'QD':[[str(a) for a in row] for row in R.tolist()],
  'cone_generators':[list(w) for w in gens],
  'cone_determinant':int(det(u,v)),
  'T':[[str(a) for a in row] for row in T.tolist()],
  'b_columns':[[str(a) for a in row] for row in B.tolist()],
  'projected_branch_coordinates':[list(w) for w in sorted(possible)]
}
out=Path(__file__).with_name('equal-weight-rounding-exact-check.json')
out.write_text(json.dumps(result,indent=2,default=int)+'\n')
print(json.dumps({'exact_checks':'passed','output':str(out),'all_K_symbolic':True}))
