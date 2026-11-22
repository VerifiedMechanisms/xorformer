"""Refine a numerical Boolean-score fiber and emit exact dyadic proof data.

The companion verifier performs only integer interval arithmetic. Floating
refinement is used to discover a center, never as an existence certificate.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp


def model(z, rows, n, h):
    vals=[];jac=[]
    for mask in rows:
        active=[i for i in range(n) if mask>>i&1]
        num=[sum(z[i*h+j] for i in active) for j in range(h)]
        den=[1+sum(z[n*h+i*h+j] for i in active) for j in range(h)]
        vals.append(1+sum(num[j]/den[j] for j in range(h)))
        jac.append([1/den[j] if i in active else 0
                    for i in range(n) for j in range(h)]+
                   [-num[j]/den[j]**2 if i in active else 0
                    for i in range(n) for j in range(h)])
    return mp.matrix(vals),mp.matrix(jac)


def main():
    p=argparse.ArgumentParser();p.add_argument('candidate',type=Path)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    d=json.loads(a.candidate.read_text());n,h=d['n'],d['heads'];rows=d['sample']
    mp.mp.dps=100
    base=[mp.mpf(v)/d['numerator_scale'] for row in d['numerator_integer'] for v in row]
    base += [mp.mpf(v)/d['denominator_scale'] for row in d['denominator_integer'] for v in row]
    target,_=model(mp.matrix(base),rows,n,h)
    z=mp.matrix([mp.mpf(v) for v in d['theta'][:n*h]]+
                [mp.exp(mp.mpf(v)) for v in d['theta'][n*h:]])
    residuals=[]
    for iteration in range(20):
        val,j=model(z,rows,n,h);res=val-target
        residuals.append(str(mp.norm(res,mp.inf)))
        if mp.norm(res,mp.inf)<mp.mpf('1e-85'): break
        z-=mp.lu_solve(j,res)
    assert mp.norm(model(z,rows,n,h)[0]-target,mp.inf)<mp.mpf('1e-80')
    center_bits=200;inverse_bits=120
    center=[int(mp.nint(v*2**center_bits)) for v in z]
    z=mp.matrix([mp.mpf(v)/2**center_bits for v in center])
    _,j=model(z,rows,n,h);inverse=j**-1
    inverse_integer=[[int(mp.nint(inverse[i,k]*2**inverse_bits))
                       for k in range(2*n*h)] for i in range(2*n*h)]
    kept={k:d[k] for k in ['n','heads','sample','numerator_integer',
          'numerator_scale','denominator_integer','denominator_scale']}
    kept.update(center_bits=center_bits,center_integer=center,
                inverse_bits=inverse_bits,inverse_integer=inverse_integer,
                radius_bits=100,interval_bits=256,
                discovery_residuals=residuals,
                status='PROOF_DATA_REQUIRES_INDEPENDENT_VERIFICATION',
                main_target_proved=False)
    a.output.write_text(json.dumps(kept,indent=2)+'\n')
    print(json.dumps({'iterations':len(residuals),'last_residual':residuals[-1],
                      'output':str(a.output)}))


if __name__=='__main__':main()
