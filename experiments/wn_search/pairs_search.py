"""Miniature Warren-tightness test: represent a random GRAPH on n vertices (sign pattern on the C(n,2)
weight-two points) by H heads: S({i,j}) = sigma + sum_h (u_{h,i}+u_{h,j})/(1+b_{h,i}+b_{h,j}).
Linear-like capacity needs 2nH ~ M/2 (H ~ n/8); Warren-tight capacity needs 2nH log(enH/ (2nH/M)...) ~ M, i.e. H ~ n/(4 log n).
"""
import sys, argparse, time, itertools, numpy as np
sys.path.insert(0, '/work/experiments/wn_search')
from search2 import alt_search, alt_search_hinge, exact_verify

def pairs(n):
    P = list(itertools.combinations(range(n), 2))
    X = np.zeros((len(P), n))
    for r, (i, j) in enumerate(P):
        X[r, i] = 1; X[r, j] = 1
    return X

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=32)
    ap.add_argument("--H", type=int, nargs="+", default=[2, 3, 4, 6, 8])
    ap.add_argument("--graphs", type=int, default=2)
    ap.add_argument("--iters", type=int, default=200)
    ap.add_argument("--restarts", type=int, default=3)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--hinge", action="store_true")
    args = ap.parse_args()
    X = pairs(args.n); M = X.shape[0]
    rng = np.random.default_rng(args.seed)
    print(f"n={args.n} pairs M={M}; linear-like threshold 2nH~M/2 -> H~{M/(4*args.n):.1f}; Warren H~{M/(2*args.n*np.log2(np.e*M/(2*args.n))):.1f}", flush=True)
    for g in range(args.graphs):
        s = rng.choice([-1.0, 1.0], size=M)
        for H in args.H:
            t0 = time.time()
            if args.hinge:
                t, params = alt_search_hinge(X, s, H, 0, iters=args.iters, restarts=args.restarts, seed=args.seed*100+g*10+H)
                if params is not None and t > 1.0: t = -1.0  # loss returned, not a margin
            else:
                t, params = alt_search(X, s, H, 0, iters=args.iters, restarts=args.restarts, seed=args.seed*100+g*10+H)
            ok, info = (False, None)
            if params is not None and t > 1e-7:
                ok, info = exact_verify(X, s, *params)
            print(f"graph {g} H={H} (2nH={2*args.n*H}) margin={t:.3e} exact={ok} [{time.time()-t0:.0f}s]", flush=True)
            if ok:
                break

if __name__ == "__main__":
    main()
