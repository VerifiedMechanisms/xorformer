"""Numerical diagnostic for jointly deformed sheets. Not a universality proof.

Run as heavy python3 artifacts/head-compression/reverse-deformed-geometry-probe.py.
Per-row normalization only tests one Gaussian derivative-query distribution.
Its collapse does not exclude cancellation or other query families.
"""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS'): os.environ[key]='1'
import mpmath as mp
import itertools, random, json, time
import numpy as np
mp.mp.dps=100

def run(h,epsden,seed):
    rng=random.Random(seed)
    eps=mp.mpf(1)/epsden
    lam=[eps*(j+1)/(h+1) for j in range(h)]
    d=[1-eps*(i+1)/(h+1) for i in range(h)]
    C=mp.matrix([[1/(di-lj) for lj in lam] for di in d])
    inv=C**-1
    U=mp.matrix([[rng.randrange(-100,101) for j in range(h)] for i in range(h)])
    E=C*U
    perms=list(itertools.permutations(range(h)))
    pos={p:k for k,p in enumerate(perms)}
    feats=[]
    start=time.monotonic()
    for p in perms:
        e=mp.matrix([sum(E[i,k]*C[i,p[k]] for k in range(h)) for i in range(h)])
        aordered=-(inv*e)
        a=[aordered[p[k]] for k in range(h)]
        R=[[ (E[i,k]+a[k])*C[i,p[k]]**2 for k in range(h)] for i in range(h)]
        assert max(abs(sum((E[i,k]+a[k])*C[i,p[k]] for k in range(h))) for i in range(h))<mp.mpf('1e-45')
        # Per-row normalization leaves each Gaussian-v query sign law unchanged.
        normed=[]
        for row in R:
            norm=mp.sqrt(sum(x*x for x in row))
            normed.append([float(x/norm) for x in row])
        feats.append(normed)
    f=np.asarray(feats)
    taus=[tuple((j^1) if (j^1)<h else j for j in range(h)),tuple(reversed(range(h)))]
    stats=[]
    for tau in taus:
        ids=np.array([pos[tuple(tau[j] for j in p)] for p in perms])
        cosine=np.clip(np.sum(f*f[ids],axis=2),-1,1)
        sep=np.arccos(cosine).mean(axis=1)/np.pi
        stats.append({'token_relabeling':tau,'mean_separation':float(sep.mean()),'min_separation':float(sep.min()),'quantiles':np.quantile(sep,[.01,.1,.5,.9,.99]).tolist()})
    # Compare each row embedding to the first; a near-zero difference flags collapse.
    row_deviation=np.max(np.linalg.norm(f-f[:,:1,:],axis=2))
    result={'H':h,'epsilon_denominator':epsden,'seed':seed,'permutations':len(perms),'seconds':time.monotonic()-start,'max_normalized_row_deviation':float(row_deviation),'tests':stats,'scope':'High precision numerical geometry, not a compiler proof or an obstruction.'}
    print(json.dumps(result),flush=True)
    return result
if __name__=='__main__':
    results=[run(h,d,17) for h in (4,5,6,7) for d in (100,10000)]
    open('artifacts/head-compression/reverse-deformed-geometry-results.json','w').write(json.dumps(results,indent=2)+'\n')
