"""Count real solutions of the interpolation system S(x_j; theta) = 0 for 2nH random cube points.

S(x; theta) = 1 + sum_h (u_h . x)/(1 + b_h . x), theta = (u, b) in R^{2nH}, sigma = 1 fixed.
We clear denominators: F_j(theta) = prod_h (1 + b_h.x_j) + sum_h (u_h.x_j) prod_{g != h}(1 + b_g.x_j) = 0.
Newton/Levenberg-Marquardt from many random starts; dedup converged real solutions; report how many have all b >= 0.
A large (exponential in nH) count indicates Warren-tight multiplicity; a small count indicates linear-like behaviour.
"""
import argparse, numpy as np, time
from scipy.optimize import least_squares


def cube(n):
    return np.array([[(k >> i) & 1 for i in range(n)] for k in range(2 ** n)], dtype=np.float64)


def score(X, theta, n, H):
    U = theta[:n * H].reshape(n, H); B = theta[n * H:].reshape(n, H)
    P = 1.0 + X @ B
    return 1.0 + ((X @ U) / P).sum(1), P


def make_system(X, n, H, y):
    def F(theta):
        val, P = score(X, theta, n, H)
        return val - y
    return F


def jac_rank(X, theta, n, H, eps=1e-6):
    m = X.shape[0]
    J = np.zeros((m, theta.size))
    base, _ = score(X, theta, n, H)
    for k in range(theta.size):
        t2 = theta.copy(); t2[k] += eps
        J[:, k] = (score(X, t2, n, H)[0] - base) / eps
    return np.linalg.matrix_rank(J, tol=1e-6)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=5)
    ap.add_argument("--H", type=int, default=2)
    ap.add_argument("--starts", type=int, default=3000)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--trials", type=int, default=2)
    args = ap.parse_args()
    n, H = args.n, args.H
    m = 2 * n * H
    Xall = cube(n)
    rng = np.random.default_rng(args.seed)
    for trial in range(args.trials):
        idx = rng.choice(np.arange(1, 2 ** n), size=m, replace=False)
        X = Xall[idx]
        # planted generic target so that at least one real admissible solution exists
        ustar = rng.normal(size=n * H); bstar = np.exp(rng.uniform(-2, 2, size=n * H))
        thstar = np.concatenate([ustar, bstar])
        y, _ = score(X, thstar, n, H)
        print(f"  jacobian rank at planted point: {jac_rank(X, thstar, n, H)} of {m}", flush=True)
        F = make_system(X, n, H, y)
        sols = []
        t0 = time.time()
        nconv = 0
        for s in range(args.starts):
            u0 = rng.normal(size=n * H)
            b0 = np.exp(rng.uniform(-3, 3, size=n * H))
            theta0 = np.concatenate([u0, b0])
            res = least_squares(F, theta0, method="lm", xtol=1e-14, ftol=1e-14, gtol=1e-14, max_nfev=2000)
            if res.success or np.max(np.abs(res.fun)) < 1e-9:
                th = res.x
                # verify with the uncleared score (avoid spurious solutions at poles)
                U = th[:n * H].reshape(n, H); B = th[n * H:].reshape(n, H)
                P = 1.0 + X @ B
                if np.any(np.abs(P) < 1e-6):
                    continue
                val = 1.0 + ((X @ U) / P).sum(1)
                if np.max(np.abs(val - y)) < 1e-8 and np.all(np.isfinite(th)) and np.max(np.abs(th)) < 1e8:
                    nconv += 1
                    key = tuple(np.round(th, 5))
                    # dedup up to head permutation: sort heads by first b coordinate
                    order = np.argsort(np.round(B[0], 5))
                    key = tuple(np.round(np.concatenate([U[:, order].ravel(), B[:, order].ravel()]), 4))
                    sols.append(key)
        uniq = set(sols)
        adm = sum(1 for k in uniq if min(k[n * H:]) >= -1e-6)
        print(f"n={n} H={H} unknowns={m} trial={trial} converged={nconv} distinct_real={len(uniq)} admissible={adm} [{time.time()-t0:.0f}s]", flush=True)


if __name__ == "__main__":
    main()
