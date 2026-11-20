"""Alternating LP / dual-gradient search for H-head representations.

For fixed denominators b (n x H, nonneg), the best numerators solve the LP
    maximize t  s.t.  s_x * (sigma + sum_h (u_h.x)/(1+b_h.x)) >= t,  |sigma|,|u| <= 1.
By Danskin's theorem the max-margin t(b) has subgradient
    dt/db_{i,h} = sum_x lam_x s_x * ( -(u_h.x) x_i / (1+b_h.x)^2 ),
where lam are the optimal duals (normalized, lam >= 0, sum lam = 1).
We ascend t with multiplicative updates on b (keeps b >= 0), with random restarts.
Also supports M-heads (complemented coordinates) and planted-instance diagnostics.
"""
import argparse, json, time, sys
import numpy as np
from scipy.optimize import linprog
from fractions import Fraction


def cube(n):
    return np.array([[(k >> i) & 1 for i in range(n)] for k in range(2 ** n)], dtype=np.float64)


def features(X, Bp, Dm):
    N, n = X.shape
    Y = 1.0 - X
    cols = [np.ones((N, 1))]
    if Bp.shape[1]:
        R = 1.0 / (1.0 + X @ Bp)
        cols.append((X[:, :, None] * R[:, None, :]).reshape(N, -1))
    if Dm.shape[1]:
        Q = 1.0 / (1.0 + Y @ Dm)
        cols.append((Y[:, :, None] * Q[:, None, :]).reshape(N, -1))
    return np.concatenate(cols, axis=1)


def lp_margin(Phi, s):
    N, m = Phi.shape
    A_ub = np.concatenate([-(s[:, None] * Phi), np.ones((N, 1))], axis=1)
    c = np.zeros(m + 1); c[-1] = -1.0
    bounds = [(-1.0, 1.0)] * m + [(None, 1.0)]
    res = linprog(c, A_ub=A_ub, b_ub=np.zeros(N), bounds=bounds, method="highs")
    if res.status != 0:
        return -np.inf, None, None
    w = res.x[:m]; t = res.x[-1]
    lam = -res.ineqlin.marginals
    return t, w, lam


def unpack(w, n, HP, HM):
    sigma = w[0]
    U = w[1:1 + n * HP].reshape(n, HP) if HP else np.zeros((n, 0))
    V = w[1 + n * HP:1 + n * HP + n * HM].reshape(n, HM) if HM else np.zeros((n, 0))
    return sigma, U, V


def grad_b(X, s, lam, U, Bp, V, Dm):
    N, n = X.shape
    Y = 1.0 - X
    gB = np.zeros_like(Bp); gD = np.zeros_like(Dm)
    if Bp.shape[1]:
        R2 = 1.0 / (1.0 + X @ Bp) ** 2          # N x HP
        num = X @ U                              # N x HP
        coef = (lam * s)[:, None] * (-num * R2)  # N x HP
        gB = X.T @ coef                          # n x HP
    if Dm.shape[1]:
        Q2 = 1.0 / (1.0 + Y @ Dm) ** 2
        num = Y @ V
        coef = (lam * s)[:, None] * (-num * Q2)
        gD = Y.T @ coef
    return gB, gD


def exact_verify(X, s, sigma, U, Bp, V, Dm, maxden=10 ** 12):
    N, n = X.shape
    Fr = lambda a: Fraction(float(a)).limit_denominator(maxden)
    sig = Fr(sigma)
    Uq = [[Fr(U[i, h]) for h in range(U.shape[1])] for i in range(n)]
    Bq = [[Fr(Bp[i, h]) for h in range(Bp.shape[1])] for i in range(n)]
    Vq = [[Fr(V[i, h]) for h in range(V.shape[1])] for i in range(n)]
    Dq = [[Fr(Dm[i, h]) for h in range(Dm.shape[1])] for i in range(n)]
    if any(Bq[i][h] < 0 for h in range(Bp.shape[1]) for i in range(n)): return False, "neg slope"
    if any(Dq[i][h] < 0 for h in range(Dm.shape[1]) for i in range(n)): return False, "neg slope"
    mm = None
    for k in range(N):
        x = [int(X[k, i]) for i in range(n)]
        val = sig
        for h in range(Bp.shape[1]):
            val += sum(Uq[i][h] for i in range(n) if x[i]) / (1 + sum(Bq[i][h] for i in range(n) if x[i]))
        for h in range(Dm.shape[1]):
            val += sum(Vq[i][h] for i in range(n) if not x[i]) / (1 + sum(Dq[i][h] for i in range(n) if not x[i]))
        if val * int(s[k]) <= 0:
            return False, f"fails at {k}"
        mm = abs(val) if mm is None else min(mm, abs(val))
    return True, float(mm)


def alt_search(X, s, HP, HM, iters=300, restarts=5, lr0=0.5, seed=0, tol=1e-7, verbose=False, init_scale=3.0):
    N, n = X.shape
    rng = np.random.default_rng(seed)
    best = (-np.inf, None)
    for r in range(restarts):
        Bp = np.exp(rng.uniform(-init_scale, init_scale, size=(n, HP)))
        Dm = np.exp(rng.uniform(-init_scale, init_scale, size=(n, HM)))
        lr = lr0
        last_t = -np.inf
        for it in range(iters):
            Phi = features(X, Bp, Dm)
            t, w, lam = lp_margin(Phi, s)
            if w is None:
                break
            sigma, U, V = unpack(w, n, HP, HM)
            if t > best[0]:
                best = (t, (sigma, U, Bp.copy(), V, Dm.copy()))
            if t > tol:
                if verbose: print(f"  restart {r} it {it} margin {t:.3e} SUCCESS", flush=True)
                return best
            gB, gD = grad_b(X, s, lam, U, Bp, V, Dm)
            # multiplicative (log-space) ascent with normalized direction
            g = np.concatenate([(gB * Bp).ravel(), (gD * Dm).ravel()])  # gradient wrt log b
            nrm = np.linalg.norm(g)
            if nrm < 1e-14:
                # random kick
                Bp *= np.exp(rng.normal(0, 0.3, Bp.shape)); Dm *= np.exp(rng.normal(0, 0.3, Dm.shape))
                continue
            step = lr / nrm
            Bp *= np.exp(step * gB * Bp)
            Dm *= np.exp(step * gD * Dm)
            Bp = np.clip(Bp, 1e-8, 1e8); Dm = np.clip(Dm, 1e-8, 1e8)
            if t <= last_t + 1e-12:
                lr *= 0.97
            last_t = t
            if verbose and it % 50 == 0:
                print(f"  restart {r} it {it} margin {t:.3e} lr {lr:.3f}", flush=True)
    return best


def planted(X, H0, rng, scale=3.0):
    N, n = X.shape
    B0 = np.exp(rng.uniform(-scale, scale, size=(n, H0)))
    U0 = rng.normal(size=(n, H0))
    sig0 = rng.normal()
    S = sig0 + ((X @ U0) / (1.0 + X @ B0)).sum(1)
    s = np.sign(S); s[s == 0] = 1.0
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=8)
    ap.add_argument("--H", type=int, nargs="+", default=[8])
    ap.add_argument("--funcs", type=int, default=3)
    ap.add_argument("--iters", type=int, default=300)
    ap.add_argument("--restarts", type=int, default=5)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--mixed", action="store_true")
    ap.add_argument("--planted", type=int, default=0, help="if >0, generate targets from a random model with this many heads")
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    n = args.n; X = cube(n); rng = np.random.default_rng(args.seed)
    results = []
    for fi in range(args.funcs):
        if args.planted:
            s = planted(X, args.planted, rng)
        else:
            s = rng.choice([-1.0, 1.0], size=2 ** n)
        rec = {"n": n, "func": fi, "planted": args.planted, "results": {}}
        for H in args.H:
            HP, HM = ((H + 1) // 2, H // 2) if args.mixed else (H, 0)
            t0 = time.time()
            t, params = alt_search(X, s, HP, HM, iters=args.iters, restarts=args.restarts,
                                   seed=args.seed * 1000 + fi * 10 + H, verbose=args.verbose)
            ok, info = (False, None)
            if params is not None and t > 1e-7:
                ok, info = exact_verify(X, s, *params)
            dt = time.time() - t0
            rec["results"][H] = {"lp_margin": float(t), "exact_ok": bool(ok), "info": str(info), "sec": dt}
            if ok:
                sg, Un, Bp, Vn, Dm = params
                rec["results"][H]["params"] = {"sigma": float(sg), "U": Un.tolist(), "B": Bp.tolist(), "V": Vn.tolist(), "D": Dm.tolist()}
                rec["truth"] = [int(v) for v in s]
            print(f"n={n} func={fi} planted={args.planted} H={H} (P={HP},M={HM}) margin={t:.3e} exact={ok} {info} [{dt:.0f}s]", flush=True)
            if ok:
                break
        results.append(rec)
    if args.out:
        json.dump(results, open(args.out, "w"), indent=1)


if __name__ == "__main__":
    main()
