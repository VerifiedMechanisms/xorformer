"""Heuristic search for H-head representations of random Boolean functions.

Model (normalized rational normal form, Theorem 2.6 of the paper):
    S(x) = sigma + sum_{h in P} (u_h . x)/(1 + b_h . x) + sum_{h in M} (v_h . y)/(1 + d_h . y),
    y = 1 - x,  b_h, d_h >= 0 componentwise.
P-heads have positive slopes, M-heads negative slopes (written in complemented variables).
f is represented iff s_x S(x) > 0 for all x, s_x = 2f(x)-1.

Strategy: Adam on a smooth margin loss over all parameters, then an exact LP in the numerators
(denominators fixed) maximizing the minimum margin; finally exact rational verification.
"""
import argparse, json, math, sys, time
from fractions import Fraction
import numpy as np
import torch
from scipy.optimize import linprog

torch.set_default_dtype(torch.float64)


def cube(n):
    X = np.array([[(k >> i) & 1 for i in range(n)] for k in range(2 ** n)], dtype=np.float64)
    return X


def score_np(X, sigma, U, Bp, V, Dm):
    # X: N x n ; U,Bp: n x HP ; V,Dm: n x HM
    Y = 1.0 - X
    S = np.full(X.shape[0], sigma, dtype=np.float64)
    if U.shape[1] > 0:
        S = S + ((X @ U) / (1.0 + X @ Bp)).sum(1)
    if V.shape[1] > 0:
        S = S + ((Y @ V) / (1.0 + Y @ Dm)).sum(1)
    return S


def lp_numerators(X, s, Bp, Dm):
    """Given denominators, maximize min margin t over (sigma,U,V) with box |.|<=1.
    Returns (t, sigma, U, V, duals)."""
    N, n = X.shape
    Y = 1.0 - X
    HP, HM = Bp.shape[1], Dm.shape[1]
    feats = [np.ones((N, 1))]
    if HP:
        R = 1.0 / (1.0 + X @ Bp)  # N x HP
        feats.append((X[:, :, None] * R[:, None, :]).reshape(N, n * HP))
    if HM:
        Q = 1.0 / (1.0 + Y @ Dm)
        feats.append((Y[:, :, None] * Q[:, None, :]).reshape(N, n * HM))
    Phi = np.concatenate(feats, axis=1)  # N x m
    m = Phi.shape[1]
    # variables: w (m), t ; maximize t  <=> minimize -t
    # constraints: -s_x Phi(x) . w + t <= 0
    A_ub = np.concatenate([-(s[:, None] * Phi), np.ones((N, 1))], axis=1)
    b_ub = np.zeros(N)
    c = np.zeros(m + 1)
    c[-1] = -1.0
    bounds = [(-1.0, 1.0)] * m + [(None, 1.0)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if res.status != 0:
        return -np.inf, None, None, None, None
    w = res.x[:m]
    t = res.x[-1]
    sigma = w[0]
    U = w[1:1 + n * HP].reshape(n, HP) if HP else np.zeros((n, 0))
    V = w[1 + n * HP:].reshape(n, HM) if HM else np.zeros((n, 0))
    duals = None
    try:
        duals = -res.ineqlin.marginals  # >= 0
    except Exception:
        pass
    return t, sigma, U, V, duals


def exact_verify(X, s, sigma, U, Bp, V, Dm, maxden=10 ** 9):
    """Exact rational check of strict sign agreement."""
    N, n = X.shape
    Fr = lambda a: Fraction(float(a)).limit_denominator(maxden)
    sig = Fr(sigma)
    Uq = [[Fr(U[i, h]) for h in range(U.shape[1])] for i in range(n)]
    Bq = [[Fr(Bp[i, h]) for h in range(Bp.shape[1])] for i in range(n)]
    Vq = [[Fr(V[i, h]) for h in range(V.shape[1])] for i in range(n)]
    Dq = [[Fr(Dm[i, h]) for h in range(Dm.shape[1])] for i in range(n)]
    for h in range(Bp.shape[1]):
        for i in range(n):
            if Bq[i][h] < 0:
                return False, "negative slope"
    for h in range(Dm.shape[1]):
        for i in range(n):
            if Dq[i][h] < 0:
                return False, "negative slope"
    minmargin = None
    for k in range(N):
        x = [int(X[k, i]) for i in range(n)]
        val = sig
        for h in range(Bp.shape[1]):
            num = sum(Uq[i][h] for i in range(n) if x[i])
            den = 1 + sum(Bq[i][h] for i in range(n) if x[i])
            val += num / den
        for h in range(Dm.shape[1]):
            num = sum(Vq[i][h] for i in range(n) if not x[i])
            den = 1 + sum(Dq[i][h] for i in range(n) if not x[i])
            val += num / den
        if val * int(s[k]) <= 0:
            return False, f"sign fails at x index {k}"
        mm = abs(val)
        minmargin = mm if minmargin is None else min(minmargin, mm)
    return True, float(minmargin)


def search(X, s, HP, HM, steps=3000, restarts=4, lr=0.05, seed=0, verbose=False, lp_every=500):
    N, n = X.shape
    Xt = torch.tensor(X)
    Yt = 1.0 - Xt
    st = torch.tensor(s)
    best = (-np.inf, None)
    g = torch.Generator().manual_seed(seed)
    for r in range(restarts):
        sigma = torch.zeros(1, requires_grad=True)
        U = (0.5 * torch.randn(n, HP, generator=g)).requires_grad_(True)
        V = (0.5 * torch.randn(n, HM, generator=g)).requires_grad_(True)
        # denominators: b = exp(beta), log-uniform init over a wide dynamic range
        beta = (torch.rand(n, HP, generator=g) * 8.0 - 4.0).requires_grad_(True)
        delta = (torch.rand(n, HM, generator=g) * 8.0 - 4.0).requires_grad_(True)
        opt = torch.optim.Adam([sigma, U, V, beta, delta], lr=lr)
        kappa = 5.0
        for it in range(steps):
            opt.zero_grad()
            S = sigma.expand(N)
            if HP:
                S = S + ((Xt @ U) / (1.0 + Xt @ torch.exp(beta))).sum(1)
            if HM:
                S = S + ((Yt @ V) / (1.0 + Yt @ torch.exp(delta))).sum(1)
            marg = st * S
            # scale-free margin: normalize by numerator norm
            scale = torch.sqrt(sigma ** 2 + (U ** 2).sum() + (V ** 2).sum() + 1e-12)
            z = marg / scale
            loss = torch.nn.functional.softplus(kappa * (0.5 - z)).mean() / kappa
            loss.backward()
            opt.step()
            if (it + 1) % lp_every == 0 or it == steps - 1:
                with torch.no_grad():
                    Bp = torch.exp(beta).numpy().copy() if HP else np.zeros((n, 0))
                    Dm = torch.exp(delta).numpy().copy() if HM else np.zeros((n, 0))
                t, sg, Un, Vn, _ = lp_numerators(X, s, Bp, Dm)
                if verbose:
                    print(f"  restart {r} it {it+1} loss {loss.item():.4f} lp-margin {t:.3e}", flush=True)
                if t > best[0]:
                    best = (t, (sg, Un, Bp, Vn, Dm))
                if t > 1e-7:
                    return best
    return best


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=8)
    ap.add_argument("--H", type=int, nargs="+", default=[8])
    ap.add_argument("--funcs", type=int, default=5)
    ap.add_argument("--steps", type=int, default=3000)
    ap.add_argument("--restarts", type=int, default=3)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--mixed", action="store_true", help="use half P-heads and half M-heads")
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    n = args.n
    X = cube(n)
    rng = np.random.default_rng(args.seed)
    results = []
    for fi in range(args.funcs):
        s = rng.choice([-1.0, 1.0], size=2 ** n)
        rec = {"n": n, "func": fi, "results": {}}
        for H in args.H:
            if args.mixed:
                HP, HM = (H + 1) // 2, H // 2
            else:
                HP, HM = H, 0
            t0 = time.time()
            t, params = search(X, s, HP, HM, steps=args.steps, restarts=args.restarts,
                               seed=args.seed * 1000 + fi * 10 + H, verbose=args.verbose)
            ok, info = (False, None)
            if params is not None and t > 1e-7:
                ok, info = exact_verify(X, s, *params)
            dt = time.time() - t0
            rec["results"][H] = {"lp_margin": float(t), "exact_ok": bool(ok), "info": str(info), "sec": dt}
            if ok:
                sg, Un, Bp, Vn, Dm = params
                rec["results"][H]["params"] = {"sigma": float(sg), "U": Un.tolist(), "B": Bp.tolist(),
                                               "V": Vn.tolist(), "D": Dm.tolist()}
                rec["truth"] = [int(v) for v in s]
            print(f"n={n} func={fi} H={H} (P={HP},M={HM}) lp-margin={t:.3e} exact={ok} {info} [{dt:.0f}s]", flush=True)
            if ok:
                break
        results.append(rec)
    if args.out:
        with open(args.out, "w") as fh:
            json.dump(results, fh, indent=1)


if __name__ == "__main__":
    main()
