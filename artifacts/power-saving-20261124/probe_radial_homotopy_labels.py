"""Find an exact finite-t/flat-limit sign separation for fixed radial poles."""
import itertools,json
from pathlib import Path
import numpy as np
import sympy as s
from scipy.optimize import linprog
X=np.array([[1,*x] for x in itertools.product([0,1],repeat=4)],dtype=np.int64)
rng=np.random.default_rng(202611241048)
for trial in range(100):
    c1=np.r_[0,rng.integers(1,8,4)]
    c2=np.r_[0,rng.integers(1,8,4)]
    delta=c2-c1
    if np.count_nonzero(delta[1:])<3:continue
    d=X@delta
    F=np.column_stack([X,d[:,None]*X[:,1:]])
    if np.linalg.matrix_rank(F)<9:continue
    for j in range(100):
        a1=rng.integers(-10,11,5);a2=rng.integers(-10,11,5)
        B1=1+X@c1;B2=1+X@c2
        P=(X@a1)*B2+(X@a2)*B1
        if np.any(P==0):continue
        y=np.sign(P)
        res=linprog(np.zeros(9),A_ub=-y[:,None]*F,b_ub=-np.ones(16),bounds=[(None,None)]*9,method='highs')
        if res.success:continue
        T=s.Matrix((y[:,None]*F).tolist()).T
        dual=linprog(np.zeros(16),A_eq=np.vstack([np.array(T,dtype=float),np.ones(16)]),b_eq=np.r_[np.zeros(9),1],bounds=[(0,None)]*16,method='highs')
        if not dual.success:continue
        supp=np.flatnonzero(dual.x>1e-8).tolist()
        M=T[:,supp].col_join(s.ones(1,len(supp)))
        rhs=s.zeros(T.rows,1).col_join(s.ones(1,1))
        sol,params=M.gauss_jordan_solve(rhs)
        if params.rows:sol=sol.subs({z:0 for z in params})
        if not all(z>=0 for z in sol):continue
        assert M*sol==rhs
        lam=[s.Rational(0)]*16
        for i,z in zip(supp,sol):lam[i]=z
        assert T*s.Matrix(lam)==s.zeros(9,1) and sum(lam)==1
        result={'scope':'Finite exact fixed-direction radial homotopy counterexample, not an unrestricted lower bound.',
                'c1':c1.tolist(),'c2':c2.tolist(),'delta':delta.tolist(),'a1':a1.tolist(),'a2':a2.tolist(),
                'cleared_table':P.tolist(),'target':y.tolist(),'dual':[str(z) for z in lam],
                'dual_support':supp,'flat_rank':9}
        out=Path(__file__).with_name('radial-homotopy-exact-separation.json')
        out.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result));raise SystemExit
raise SystemExit('No separation found in finite probe')
