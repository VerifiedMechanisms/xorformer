"""Two-variable continuous miniature: points on an M x M grid in [0,1]^2, heads (u.x)/(1+b.x), b >= 0.
Linear-like capacity needs 2H+1 (numerator dims) ~ M^2/2; Warren-like needs 4H log(e M^2) ~ M^2.
This tests whether the non-perturbative sum-of-ratios family is Warren-like in n = 2 continuous variables,
where the Chow variety of products of H affine forms has exponential degree (2H-1)!!.
"""
import sys, argparse, time, numpy as np
sys.path.insert(0, '/work/experiments/wn_search')
from search2 import alt_search_hinge, exact_verify

def grid(M):
    g = np.linspace(0.0, 1.0, M)
    X = np.array([[a, b] for a in g for b in g])
    return X

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=12)
    ap.add_argument("--H", type=int, nargs="+", default=[4, 6, 8, 12, 16, 24, 32])
    ap.add_argument("--funcs", type=int, default=2)
    ap.add_argument("--iters", type=int, default=300)
    ap.add_argument("--restarts", type=int, default=3)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    X = grid(args.M); P = X.shape[0]
    rng = np.random.default_rng(args.seed)
    print(f"grid M={args.M}: P={P} points; linear-like H ~ {P/4:.0f} (2H+1 ~ P/2); Warren-like H ~ {P/(4*np.log2(np.e*P)):.1f}", flush=True)
    for fi in range(args.funcs):
        s = rng.choice([-1.0, 1.0], size=P)
        for H in args.H:
            t0 = time.time()
            t, params = alt_search_hinge(X, s, H, 0, iters=args.iters, restarts=args.restarts, seed=args.seed*100+fi*10+H)
            ok = False
            if params is not None and 0 < t < 1.0:
                ok, info = exact_verify(X, s, *params)
            print(f"func {fi} H={H} (params {4*H+1}) result={t:.3e} exact={ok} [{time.time()-t0:.0f}s]", flush=True)
            if ok: break

if __name__ == "__main__":
    main()
