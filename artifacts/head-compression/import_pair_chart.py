#!/usr/bin/env python3
"""Import pair searches into the shared-affine chart without changing labels.

Nonzero stable pairs have an exact algebraic conversion. A confluent pair
is approximated by two separated denominators; this is only a warm start,
and its measured discrepancy is recorded. Neither import is a certificate.
"""
import argparse
import json
import os
from pathlib import Path
from tempfile import TemporaryDirectory

for key in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS"):
    os.environ[key] = "1"
import numpy as np
from search_shared_affine_varpro import initialize, features
from search_stable_pair_varpro import score_gradient as stable_score
from search_confluent_varpro import score_gradient as confluent_score


def import_chart(path, out):
    saved = np.load(path)
    labels, ori, logs, coefficient = [saved[k].copy() for k in
                                     ("labels","orientation","logs","coefficients")]
    units, n = logs.shape
    x = ((np.arange(len(labels))[:,None] >> np.arange(n)) & 1).astype(float)
    t = np.where(ori[None,:,None] > 0,x[:,None],1-x[:,None])
    cc, uu = coefficient[1:].reshape(2,units,n)
    candidates = []
    if "epsilon" in saved:
        eps, w = saved["epsilon"], saved["w"]
        assert np.all(eps != 0), "Zero stable separations need a confluent approximation."
        old = stable_score(t,labels,logs,w,eps,coefficient)[1]
        candidates.append(("exact nonzero stable-pair identity",eps.copy(),
                           logs+eps[:,None]*w))
    else:
        v = saved["v"]
        old = confluent_score(t,labels,logs,v,coefficient)[1]
        b = np.exp(logs)
        size = np.maximum(np.max(np.abs(v/b),axis=1),1.)
        for relative in (1e-2,1e-3,1e-4,1e-5,1e-6):
            eps = relative/size
            second = b+eps[:,None]*v
            assert np.all(second>0)
            candidates.append((f"confluent warm start, relative separation {relative}",
                               eps,np.log(second)))
    trials, best = [], None
    with TemporaryDirectory() as tmp:
        ordinary = Path(tmp)/"ordinary.npz"
        for mechanism, eps, second_logs in candidates:
            pair_logs = np.stack((logs,second_logs),axis=1).reshape(2*units,n)
            a1, a2 = cc+uu/eps[:,None], -uu/eps[:,None]
            pair_coeff = np.r_[coefficient[0],np.stack((a1,a2),axis=1).ravel()]
            np.savez(ordinary,labels=labels,orientation=np.repeat(ori,2),
                     logs=pair_logs,coefficients=pair_coeff)
            yy,ll,ss,cf = initialize(ordinary)
            assert np.array_equal(yy,labels)
            score = features(x,ll,ss)@cf
            error = float(np.max(np.abs(score-old)))
            event = dict(mechanism=mechanism,maximum_score_discrepancy=error,
                         original_errors=int((labels*old<=0).sum()),
                         imported_errors=int((labels*score<=0).sum()),
                         positive_units=int((ss>0).sum()),negative_units=int((ss<0).sum()))
            trials.append(event)
            if best is None or error<best[0]:
                best=(error,ll,ss,cf,event)
    _,ll,ss,cf,event=best
    np.savez(out,labels=labels,logs=ll,separation=ss,coefficients=cf,kind="shared-affine")
    report=dict(source=str(path),output=str(out),n=n,original_pair_units=units,
                shared_units=2*units,lifted_heads=2*units+1,selected=event,trials=trials,
                labels_unchanged=True,scope="Warm start only. No target signs are certified by this import.")
    out.with_suffix(".json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report),flush=True)
    return report


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkpoint",type=Path)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    args.out.parent.mkdir(parents=True,exist_ok=True)
    import_chart(args.checkpoint,args.out)
