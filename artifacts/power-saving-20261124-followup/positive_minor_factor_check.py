import sympy as s,itertools,json
u=s.symbols('u0:3');v=s.symbols('v0:3')
delta=lambda i,j:u[j]*(1+v[i])-v[j]*(1+u[i])
Delta=-(delta(0,1)*delta(1,2)*delta(2,0)+delta(1,0)*delta(2,1)*delta(0,2))
rows=[]
for x in itertools.product([0,1],repeat=3):
 if not any(x):continue
 B=1+sum(a*b for a,b in zip(x,u));C=1+sum(a*b for a,b in zip(x,v))
 rows.append([B*C]+[a*C for a in x]+[a*B for a in x])
M=s.polys.matrices.DomainMatrix.from_Matrix(s.Matrix(rows)).convert_to(s.QQ.poly_ring(*(u+v)))
det=M.det().as_expr()
assert s.expand(det+Delta)==0
print('exact_cyclic_formula_verified', True)
print('degree',s.Poly(det,*(u+v)).total_degree())
print('number_monomials',len(s.Poly(det,*(u+v)).terms()))
for U,V in [([4,9,36],[10,13,46]),([3,5,7],[21,33,40]),([12,38,39],[13,41,42])]:
 val=int(Delta.subs(dict(zip(u+v,U+V))))
 print({'u':U,'v':V,'cleared_determinant':-val,'u_increasing':all(U[i]<U[i+1] for i in range(2)),'v_increasing':all(V[i]<V[i+1] for i in range(2)),'coordinate_order':all(a<b for a,b in zip(U,V)),'ratio_order':all(U[i]*V[i+1]<U[i+1]*V[i] for i in range(2))})
