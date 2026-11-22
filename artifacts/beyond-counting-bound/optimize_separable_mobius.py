"""Jointly optimize reciprocal tests and positive witnesses.

Numerical failure is UNKNOWN. Each reported collection is checked with exact
Fraction arithmetic by the independent evaluator in evolve_separable_mobius.
The search concerns a relaxation, not the attention-head lower bound.
"""
import argparse
import json
from pathlib import Path
import time

import numpy as np
import torch

from evolve_separable_mobius import verify


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seconds', type=float, default=3600)
    ap.add_argument('--seed', type=int, default=220261122)
    args = ap.parse_args()
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    torch.manual_seed(args.seed)
    rng = np.random.default_rng(args.seed)
    source = json.loads(args.source.read_text())
    poles = np.array(source['poles'])
    residues = np.array(source['residuals'])
    thresholds = np.array(source['thresholds'])
    m, h = poles.shape
    total = 2**m
    labels = torch.tensor([[(2*((mask >> j) & 1)-1) for j in range(m)]
                           for mask in range(total)])
    bits = (1 << np.arange(m, dtype=np.uint64))
    initial_v = np.log(poles)
    initial_w = np.concatenate([residues/poles, thresholds[:, None]], axis=1)
    initial_w /= np.linalg.norm(initial_w, axis=1)[:, None]
    initial_u = rng.uniform(-9, 9, size=(total, h))
    for mask, point in source['witnesses'].items():
        initial_u[int(mask)] = np.log(point)
    best = source.get('patterns', len(source['witnesses']))
    best_state = (initial_v.copy(), initial_w.copy(), initial_u.copy())
    started = time.monotonic()
    restart = 0
    steps = 0
    while time.monotonic()-started < args.seconds and best < total:
        v0, w0, u0 = best_state
        perturb = 0 if restart == 0 else rng.choice([.005, .02, .1, .4])
        v = torch.nn.Parameter(torch.tensor(v0+rng.normal(size=v0.shape)*perturb))
        w = torch.nn.Parameter(torch.tensor(w0+rng.normal(size=w0.shape)*perturb))
        u = torch.nn.Parameter(torch.tensor(u0+rng.normal(size=u0.shape)*perturb))
        optimizer = torch.optim.Adam([v, w, u], lr=rng.choice([.003, .01, .03]))
        target_margin = rng.choice([.002, .01, .03])
        for local in range(12000):
            if time.monotonic()-started >= args.seconds:
                break
            optimizer.zero_grad()
            wn = w / torch.linalg.vector_norm(w, dim=1, keepdim=True)
            scores = (wn[None, :, :h]*torch.sigmoid(v[None, :, :]-u[:, None, :])).sum(2)-wn[None, :, h]
            margins = labels*scores
            loss = torch.relu(target_margin-margins).square().mean()
            loss.backward()
            optimizer.step()
            with torch.no_grad():
                v.clamp_(-30, 30)
                u.clamp_(-30, 30)
                w /= torch.linalg.vector_norm(w, dim=1, keepdim=True)
            steps += 1
            if local % 100 != 0:
                continue
            with torch.no_grad():
                vv, ww, uu = v.detach().numpy(), w.detach().numpy(), u.detach().numpy()
                pp = np.exp(vv)
                rr = ww[:, :h]*pp
                cc = ww[:, h]
                xx = np.exp(uu)
                values = (rr[None, :, :]/(xx[:, None, :]+pp)).sum(2)-cc
                masks = ((values > 0).astype(np.uint64)*bits).sum(1)
                unique, indices = np.unique(masks, return_index=True)
                if len(unique) > best:
                    record = dict(poles=pp.tolist(), residuals=rr.tolist(),
                                  thresholds=cc.tolist(), patterns=len(unique),
                                  total_patterns=total, restart=restart, steps=steps,
                                  elapsed_seconds=time.monotonic()-started,
                                  status='FINITE_WITNESSES_ONLY',
                                  witnesses={str(int(mask)):xx[index].tolist()
                                             for mask,index in zip(unique,indices)})
                    try:
                        verify(record)
                    except AssertionError:
                        continue
                    best = len(unique)
                    new_u = uu.copy()
                    for mask, index in zip(unique, indices):
                        new_u[int(mask)] = uu[index]
                    best_state = (vv.copy(), ww.copy(), new_u)
                    args.output.parent.mkdir(parents=True, exist_ok=True)
                    args.output.write_text(json.dumps(record,indent=2)+'\n')
                    print(json.dumps({k:record[k] for k in ['patterns','total_patterns',
                          'restart','steps','elapsed_seconds']}),flush=True)
                    if best == total:
                        break
                if local % 1000 == 0:
                    # Search alternative basins for only the infeasible witnesses.
                    candidate_u = torch.tensor(rng.uniform(-20,20,size=(2048,h)))
                    candidate_scores = (w[None,:,:h]*torch.sigmoid(v[None,:,:]-candidate_u[:,None,:])).sum(2)-w[None,:,h]
                    candidate_margins = (labels[:,None,:]*candidate_scores[None,:,:]).amin(2)
                    maximum,index = candidate_margins.max(1)
                    existing = (labels*((w[None,:,:h]*torch.sigmoid(v[None,:,:]-u[:,None,:])).sum(2)-w[None,:,h])).amin(1)
                    change = (existing < 0) & (maximum > existing)
                    u[change] = candidate_u[index[change]]
        restart += 1
    print(json.dumps(dict(finished=True,best=best,total_patterns=total,steps=steps,
                          elapsed_seconds=time.monotonic()-started,
                          failure_status='UNKNOWN')),flush=True)


if __name__ == '__main__':
    main()
