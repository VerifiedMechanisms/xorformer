"""Independent exact validation of the retained mixed binary fiber.

No floating-point or source-search rank routine is used here. All Jacobian
entries are formed over Fraction, then cleared and reduced modulo two primes.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import prod, isqrt
import hashlib
import json


def inverse_mod(matrix, prime):
    assert all(prime%d for d in range(2,isqrt(prime)+1))
    n=len(matrix)
    a=[[v%prime for v in row]+[int(i==j) for j in range(n)] for i,row in enumerate(matrix)]
    determinant=1
    for k in range(n):
        r=next(i for i in range(k,n) if a[i][k])
        if r!=k:
            a[k],a[r]=a[r],a[k]
            determinant=-determinant
        pivot=a[k][k]
        determinant=determinant*pivot%prime
        a[k]=[(v*pow(pivot,-1,prime))%prime for v in a[k]]
        for i in range(n):
            if i==k:continue
            scale=a[i][k]
            a[i]=[(v-scale*w)%prime for v,w in zip(a[i],a[k])]
    inv=[row[n:] for row in a]
    assert all(sum(inv[i][k]*matrix[k][j] for k in range(n))%prime==int(i==j)
               for i in range(n) for j in range(n))
    return determinant,inv


def main():
    root=Path(__file__).parent
    data=json.loads((root/'integer-binary-fiber-18.json').read_text())
    n,h,scale=data['n'],data['heads'],data['numerator_scale']
    b,U=data['denominator_slopes'],data['numerator_scaled_slopes']
    samples,labels=data['sample_indices'],data['labels']
    assert (n,h,scale)==(18,3,3)
    assert len(samples)==2*n*h and len(set(samples))==len(samples)
    assert set(labels)=={-1,1}
    assert all(0<v<2**n for v in samples)
    assert all(z>0 for row in b for z in row)
    matrix=[];scores=[]
    for v,y in zip(samples,labels):
        x=[(v>>i)&1 for i in range(n)]
        den=[1+sum(b[k][i]*x[i] for i in range(n)) for k in range(h)]
        num=[sum(U[k][i]*x[i] for i in range(n)) for k in range(h)]
        score=1+sum(Q(num[k],scale*den[k]) for k in range(h))
        assert score==y
        scores.append(int(score))
        jac=[Q(x[i],den[k]) for k in range(h) for i in range(n)]
        jac += [-Q(x[i]*num[k],scale*den[k]**2) for k in range(h) for i in range(n)]
        factor=scale*prod(t*t for t in den)
        cleared=[z*factor for z in jac]
        assert all(z.denominator==1 for z in cleared)
        matrix.append([z.numerator for z in cleared])
    modular=[]
    for prime in (101,65537):
        det,inv=inverse_mod(matrix,prime)
        assert det
        modular.append(dict(prime=prime,cleared_determinant=det))
        if prime==101:
            certificate=dict(cleared_jacobian=matrix,inverse_mod_101=inv)
    # Select a six-row cloning block from coordinate zero by independent elimination.
    candidates=[i for i,v in enumerate(samples) if v&1]
    cols=[0,n,2*n,3*n,4*n,5*n]
    chosen=[];basis=[]
    for i in candidates:
        row=[matrix[i][j]%101 for j in cols]
        for k,pivot in basis:
            a=row[k]
            row=[(z-a*w)%101 for z,w in zip(row,pivot)]
        k=next((k for k,z in enumerate(row) if z),None)
        if k is None:continue
        row=[z*pow(row[k],-1,101)%101 for z in row]
        basis.append((k,row));chosen.append(i)
        if len(chosen)==6:break
    assert len(chosen)==6
    cm=[[matrix[i][j] for j in cols] for i in chosen]
    cd,ci=inverse_mod(cm,101)
    certificate.update(clone_rows=chosen,clone_columns=cols,clone_inverse_mod_101=ci)
    (root/'integer-binary-fiber-matrices.json').write_text(json.dumps(certificate)+'\n')
    report=dict(status='PASS',source_sha256=hashlib.sha256((root/'integer-binary-fiber-18.json').read_bytes()).hexdigest(),
        n=n,heads=h,samples=len(samples),positive=scores.count(1),negative=scores.count(-1),
        modular=modular,clone_rows=chosen,clone_vertices=[samples[i] for i in chosen],
        clone_cleared_determinant_mod_101=cd,main_target_proved=False,
        scope='exact finite mixed binary fiber and cloning block; no positive KKT multipliers or full-cube unit margin')
    (root/'integer-binary-fiber-checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__=='__main__':
    main()
