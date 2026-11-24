#!/usr/bin/env python3
"""Exact middle-matrix feasibility; deliberately not a Boolean sign certificate."""
from pathlib import Path
import json
import sympy as s
R=s.Rational
b=s.Matrix([2,-1,8,-1]);k=s.diag(1,-1,-1,1)
st=s.Matrix([108,2,R(212,7),58]);ell=s.Matrix([-116,0,R(660,7),0])
a=k*st+s.diag(*ell)*b
A=s.Matrix(4,4,lambda i,j:0 if i==j else sum(b)-b[i]-b[j])
L=s.Matrix(4,4,lambda i,j:0 if i==j else sum(a)-a[i]-a[j]+(ell[i]+ell[j])*A[i,j])
H=s.zeros(8);H[:4,4:]=k*A;H[4:,:4]=A*k;H[4:,4:]=L
M=s.Matrix([[1,1,R(132,7),1],[1,3,1,4],[R(132,7),1,35,3],[1,4,3,1]])
Hi=H.inv();assert Hi[:4,:4]==M
assert all(M[i,j]>abs(Hi[i,4+j])+2*abs(Hi[4+i,j]) for i in range(4) for j in range(4))
eta=R(1,1000);delta=R(1,2)
X=s.Matrix(8,8,lambda i,j: (int(i%4==j)+eta) if j<4 else (delta*(1 if i<4 else -1)*int(i%4==j-4)))
C=s.eye(8)-R(1,1000)*s.ones(8)
Y=C.T*X.inv().T*Hi
assert X*H*Y.T==C
assert all(X[i,j]>abs(X[i,j+4]) for i in range(8) for j in range(4))
assert all(Y[i,j]>abs(Y[i,j+4]) for i in range(8) for j in range(4))
assert all(C[i,j]<0 for i in range(8) for j in range(8) if i!=j)
assert all(sum(C.row(i))>0 for i in range(8))
alpha=R(1,1000)
S=st.T.col_join(X[:,:4]).col_join(Y[:,:4])*alpha
B=b.T.col_join(X[:,4:]).col_join(Y[:,4:])*alpha
assert all(S[i,j]>abs(B[i,j]) for i in range(17) for j in range(4))
assert all(sum(S[:,j])<1 for j in range(4))
U=S*k+B*s.diag(*ell)
# The normalization scales H once and X,Y once each.
assert (alpha*X)*(alpha*H)*(alpha*Y.T)==alpha**3*C

def mat(Q):return [[str(e) for e in Q.row(i)] for i in range(Q.rows)]
obj={'status':'projected coefficient feasibility only; not a Boolean sign certificate','t_index':0,'X_indices':list(range(1,9)),'Y_indices':list(range(9,17)),'k':mat(k.diagonal()),'ell':mat(ell.T),'T':'0','alpha':str(alpha),'S':mat(S),'B':mat(B),'U':mat(U),'A_unscaled':mat(A),'L_unscaled':mat(L),'H_unscaled':mat(H),'H_inverse_unscaled':mat(Hi),'X_unscaled':mat(X),'Y_unscaled':mat(Y),'C_unscaled':mat(C)}
p=Path(__file__).with_name('seed.json');p.write_text(json.dumps(obj,indent=2)+'\n')
print('Exact identities, strict pure mass inequalities, and M-matrix projected cross coefficients verified.')
print('Minimum mass gap:',min(S[i,j]-abs(B[i,j]) for i in range(17) for j in range(4)))
print('Maximum total mass:',max(sum(S[:,j]) for j in range(4)))
print('This is not a full Boolean sign certificate.')
# A second exact point also kills the degree-one coefficient in t.
st=s.Matrix([R(537039,133840),R(101,100),R(801,100),0])
ell=s.Matrix([-R(248043,83650),R(16397,47800),0,R(17712823,2342200)])
st[3]=-sum((k*st+s.diag(*ell)*b)[:3])-ell[3]*b[3]
a=k*st+s.diag(*ell)*b
assert sum(a)==0
L=s.Matrix(4,4,lambda i,j:0 if i==j else sum(a)-a[i]-a[j]+(ell[i]+ell[j])*A[i,j])
H[4:,4:]=L;Hi=H.inv();M=Hi[:4,:4]
assert all(M[i,j]>abs(Hi[i,4+j])+2*abs(Hi[4+i,j]) for i in range(4) for j in range(4))
eta=R(1,10**6)
X=s.Matrix(8,8,lambda i,j: (int(i%4==j)+eta) if j<4 else (R(1,2)*(1 if i<4 else -1)*int(i%4==j-4)))
C=s.eye(8)-R(1,10**6)*s.ones(8)
Y=C.T*X.inv().T*Hi
assert X*H*Y.T==C
assert all(X[i,j]>abs(X[i,j+4]) for i in range(8) for j in range(4))
assert all(Y[i,j]>abs(Y[i,j+4]) for i in range(8) for j in range(4))
alpha=R(1,32)
S=st.T.col_join(X[:,:4]).col_join(Y[:,:4])*alpha
B=b.T.col_join(X[:,4:]).col_join(Y[:,4:])*alpha
assert all(S[i,j]>abs(B[i,j]) for i in range(17) for j in range(4))
assert all(sum(S[:,j])<1 for j in range(4))
U=S*k+B*s.diag(*ell)
assert sum(U.row(0))==0
obj={'status':'projected coefficient feasibility and zero t-linear coefficient only; not a Boolean sign certificate','t_index':0,'X_indices':list(range(1,9)),'Y_indices':list(range(9,17)),'k':mat(k.diagonal()),'ell':mat(ell.T),'T':'0','alpha':str(alpha),'S':mat(S),'B':mat(B),'U':mat(U),'A_unscaled':mat(A),'L_unscaled':mat(L),'H_unscaled':mat(H),'H_inverse_unscaled':mat(Hi),'X_unscaled':mat(X),'Y_unscaled':mat(Y),'C_unscaled':mat(C)}
Path(__file__).with_name('seed_zero_t_linear.json').write_text(json.dumps(obj,indent=2)+'\n')
print('Second exact point also has zero sum of t numerator coefficients.')
print('Maximum total mass:',max(sum(S[:,j]) for j in range(4)))
