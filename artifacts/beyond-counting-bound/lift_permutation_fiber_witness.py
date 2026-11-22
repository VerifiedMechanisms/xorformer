"""Turn an exact local Cauchy-fiber certificate into rational strict signs.

The perturbation size is explicit. All final reciprocal predicates and every
witness are independently evaluated with fractions, without numerical roots.
"""
import argparse
from fractions import Fraction as Q
import json
import math
from pathlib import Path

import sympy as sp

from evolve_separable_mobius import verify


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    source=json.loads(args.source.read_text())
    assert source['solver_result']=='sat' and source['exact_linear_verified']
    p=list(map(sp.Rational,source['poles']))
    t=list(map(sp.Rational,source['locations']))
    permutations=source['permutations']; m=len(p); h=len(t)
    assert h in (3,4) and len(permutations)==math.factorial(h)
    offsets=source['offsets']; gradients=sp.Matrix(source['gradient'])
    top_inverse=gradients[:h,:].inv()
    alphas=[]; betas=[]; gammas=[]; ranks=[]
    for q in range(m):
        M=sp.Matrix([[1/(t[perm[i]]+p[q]) for i in range(h)] +
                    [-1/(t[perm[i]]+p[q])**2 for i in range(h)] + [-1]
                    for perm in permutations])
        target=sp.Matrix([0 if q<h else sp.Rational(row[q-h]) for row in offsets])
        sol,free=M.gauss_jordan_solve(target)
        sol=sol.subs({v:0 for v in free})
        rank=M.rank()
        assert M*sol==target and rank==2*h-1
        alphas.append(list(sol[:h])); betas.append(list(sol[h:2*h])); gammas.append(sol[-1]); ranks.append(rank)
    raw_directions=[]
    for values,branch in zip(source['witnesses'],source['chosen_branches']):
        canonical=top_inverse*sp.Matrix(list(map(sp.Rational,values)))
        raw_directions.append([canonical[j] for j in permutations[branch]])

    # Bounds for positive residues, poles and witness parameters.
    bounds=[sp.Rational(1)]
    for q in range(m):
        bounds += [1/(2*(1+abs(a))) for a in alphas[q]]
        bounds += [p[q]/(2*(1+abs(b))) for b in betas[q]]
    R=sp.Rational(0)
    minimum_linear_margin=None
    for mask,(v,branch) in enumerate(zip(raw_directions,source['chosen_branches'])):
        perm=permutations[branch]
        bounds += [t[perm[i]]/(2*(1+abs(v[i]))) for i in range(h)]
        for q in range(m):
            remainder=sp.Rational(0); linear=-gammas[q]
            for i in range(h):
                d=t[perm[i]]+p[q]; w=betas[q][i]+v[i]; a=alphas[q][i]
                linear += a/d-w/d**2
                remainder += 2*abs(w)*(abs(w)+abs(a)*d)/d**3
            signed=(1 if (mask>>q)&1 else -1)*linear
            assert signed>=1
            minimum_linear_margin=signed if minimum_linear_margin is None else min(minimum_linear_margin,signed)
            R=max(R,remainder)
    bounds.append(1/(2*(1+R))); epsilon=min(bounds)
    assert epsilon>0 and epsilon*R<sp.Rational(1,2)
    record=dict(
        poles=[[str(p[q]+epsilon*b) for b in betas[q]] for q in range(m)],
        residuals=[[str(1+epsilon*a) for a in alphas[q]] for q in range(m)],
        thresholds=[str(sum(1/(tj+p[q]) for tj in t)+epsilon*gammas[q]) for q in range(m)],
        witnesses={str(mask):[str(t[permutations[branch][i]]+epsilon*v[i]) for i in range(h)]
                   for mask,(v,branch) in enumerate(zip(raw_directions,source['chosen_branches']))},
        patterns=2**m,total_patterns=2**m,
        status='EXACT_RATIONAL_WITNESSES',
        mechanism='permutation fiber and explicit first-order perturbation',
        epsilon=str(epsilon), remainder_bound=str(R),
        minimum_linear_margin=str(minimum_linear_margin),
        perturbation_alphas=[[str(x) for x in row] for row in alphas],
        perturbation_betas=[[str(x) for x in row] for row in betas],
        perturbation_gammas=list(map(str,gammas)),
        offset_matrix_ranks=ranks,
        source=str(args.source))
    assert all(Q(x)>0 for row in record['residuals'] for x in row)
    verify(record)
    minimum=min(abs(sum(Q(r)/(Q(x)+Q(pole)) for x,r,pole in zip(point,record['residuals'][q],record['poles'][q]))-Q(record['thresholds'][q]))
                for point in record['witnesses'].values() for q in range(m))
    assert minimum>=Q(str(epsilon))/2
    record['minimum_absolute_value']=str(minimum)
    record['all_residuals_positive']=True
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'exact_rational_verified':True,'patterns':2**m,
                      'all_residuals_positive':True,'epsilon_digits':len(str(epsilon)),
                      'certificate_bytes':args.output.stat().st_size}),flush=True)


if __name__=='__main__':
    main()
