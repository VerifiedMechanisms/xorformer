"""Exploratory floating point dual norm; no lower-bound certificate."""
import numpy as np, scipy.optimize as so, itertools, json, time
n=4; X=np.array(list(itertools.product([0.,1.],repeat=n))); v=np.array([1.,1.,0.,0.]); iv=int(np.where((X==v).all(axis=1))[0][0]); outside=np.arange(16)!=iv
rng=np.random.default_rng(192701)
best=None

def calc(z, detail=False):
    w=np.exp(z.reshape(2,n)); den=np.array([1+X@w[0],1+(1-X)@w[1]]).T
    F=np.column_stack([np.ones(16),X/den[:,0,None],X/den[:,1,None]])
    # Column normalization helps LP reliability without changing function space.
    scale=np.linalg.norm(F,axis=0); F=F/scale
    U,s,V=np.linalg.svd(F,full_matrices=False); Q=U[:,s>1e-11*s[0]]
    A=np.vstack([Q[outside],-Q[outside]])
    res=so.linprog(-Q[iv],A_ub=A,b_ub=np.ones(30),bounds=[(None,None)]*Q.shape[1],method='highs')
    if not res.success:return 1e8 if not detail else {'error':res.message}
    peak=-res.fun
    if detail:return {'peak':float(peak),'logweights':z.tolist(),'scores':(Q@res.x).tolist(),'dual':res.ineqlin.marginals.tolist(),'singular':s.tolist()}
    return -peak
for k in range(40):
    z=rng.uniform(-15,15,8) if k else np.array([0.,0.,10.,10.,10.,10.,0.,0.])
    opt=so.minimize(calc,z,method='Nelder-Mead',options={'maxiter':1200,'xatol':1e-6,'fatol':1e-7},bounds=[(-25,25)]*8)
    r=calc(opt.x,True)
    if 'peak'in r and(best is None or r['peak']>best['peak']):
        best=r; print(k,json.dumps(best),flush=True)
print(json.dumps({'status':'floating exploratory only','best':best}))
