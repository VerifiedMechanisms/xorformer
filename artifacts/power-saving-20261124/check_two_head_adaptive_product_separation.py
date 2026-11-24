"""Independent exact audit of an adaptive two-product compilation barrier.

Only Fraction arithmetic is used. Numerical search is not imported. The
checker verifies the finite 6-by-32 sign certificate and a compilation into
two globally positive coherent affine denominators on 38 Boolean inputs.
The universal rank obstruction is proved separately in the accompanying note.
"""
from fractions import Fraction as F
from pathlib import Path
import json

root = Path(__file__).parent
data = json.loads((root/'two_head_six_row_sign_rank_candidate.json').read_text())
u,z,r,t = ([F(x) for x in data[k]] for k in ('u','z','r','t'))
witnesses = {int(k):v for k,v in data['witnesses'].items()}
assert len(u)==len(z)==len(r)==len(t)==6
assert set(witnesses)==set(range(32))
codes = [witnesses[j]['code'] for j in range(32)]
assert {min(code,63-code) for code in codes}==set(range(32))
columns = [[F(x) for x in witnesses[j]['parameters']] for j in range(32)]
minimum_margin = None
for j,(v,q,s,w) in enumerate(columns):
    assert min(u)+v>0 and min(z)+q>0
    for i in range(6):
        score=(r[i]+s)/(u[i]+v)+(t[i]+w)/(z[i]+q)
        assert score != 0
        assert (score>0)==bool(codes[j] & (1<<i))
        minimum_margin=abs(score) if minimum_margin is None else min(minimum_margin,abs(score))

vmin=min(row[0] for row in columns)
qmin=min(row[1] for row in columns)
eps=min(min(u)+vmin,min(z)+qmin)/4
constants=[min(u)+vmin-2*eps,min(z)+qmin-2*eps]
slopes1=[a-min(u)+eps for a in u]+[row[0]-vmin+eps for row in columns]
slopes2=[a-min(z)+eps for a in z]+[row[1]-qmin+eps for row in columns]
assert min(constants+slopes1+slopes2)>0
for j,(v,q,s,w) in enumerate(columns):
    for i in range(6):
        assert constants[0]+slopes1[i]+slopes1[6+j]==u[i]+v
        assert constants[1]+slopes2[i]+slopes2[6+j]==z[i]+q

# A bias delta*sqrt(2) is irrational, whereas every unperturbed cube score
# is rational. Hence it strictifies the entire cube. Since sqrt(2)<2,
# its magnitude is smaller than half the certified selected-point margin.
delta=minimum_margin/4
assert delta>0 and 2*delta<minimum_margin
report={
    'all_192_signs_verified':True,
    'all_32_antipodal_classes_verified':True,
    'cube_dimension':38,
    'original_head_count':2,
    'sign_rank_lower_bound':6,
    'two_affine_product_atoms_plus_bias_rank_upper_bound':5,
    'strictly_positive_denominator_constants':list(map(str,constants)),
    'smallest_denominator_slope':str(min(slopes1+slopes2)),
    'selected_point_margin':str(minimum_margin),
    'irrational_bias_coefficient_delta':str(delta),
    'bias':'delta*sqrt(2)',
    'numerical_solver_used_by_checker':False,
}
print(json.dumps(report,indent=2))
