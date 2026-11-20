"""Tropical (dominance) sub-model search.

Head h = a permutation pi_h of [n]; its n slabs are Sigma_{h,k} = {x : top_{pi_h}(supp x) = pi_h(k)}.
A global priority rank over the nH slabs and a sign per slab. f(x) = sign of the highest-priority
slab containing x (x = 0 handled separately). This is the K -> infinity limit of P-heads with
exponent-spread parameters, so a tropical representation with H heads gives H*(f) <= H.
We search (simulated annealing over permutations and priorities) for the minimum H that makes all
finalizer fibers monochromatic for random f.
"""
import argparse, numpy as np, time, math


def cube_supports(n):
    N = 2 ** n
    X = np.array([[(k >> i) & 1 for i in range(n)] for k in range(N)], dtype=np.int64)
    return X


def finalizer(X, perms, prio):
    """perms: H x n arrays (perm[h][k] = coordinate at position k); prio: H x n priorities (higher wins).
    Returns for each nonzero x the index (h*n + k) of its finalizing slab."""
    N, n = X.shape
    H = perms.shape[0]
    # position of each coordinate in each perm
    pos = np.zeros((H, n), dtype=np.int64)
    for h in range(H):
        pos[h, perms[h]] = np.arange(n)
    # for each x and head: k_h(x) = min position among support
    best_rule = np.full(N, -1, dtype=np.int64)
    best_pr = np.full(N, -np.inf)
    for h in range(H):
        P = np.where(X == 1, pos[h][None, :], n + 1)  # N x n
        k = P.min(1)  # top position (n+1 for x=0)
        pr = np.where(k <= n - 1, prio[h, np.minimum(k, n - 1)], -np.inf)
        upd = pr > best_pr
        best_pr[upd] = pr[upd]
        best_rule[upd] = h * n + k[upd]
    return best_rule


def conflicts(X, s, perms, prio):
    rule = finalizer(X, perms, prio)
    # fibers must be monochromatic; count minimal flips: for each rule, min(#plus, #minus)
    cost = 0
    H, n = perms.shape
    for r in range(H * n):
        idx = np.where(rule == r)[0]
        if idx.size == 0:
            continue
        pl = int((s[idx] > 0).sum()); mi = idx.size - pl
        cost += min(pl, mi)
    return cost


def anneal(X, s, H, iters=20000, seed=0, T0=1.0, T1=0.02):
    rng = np.random.default_rng(seed)
    N, n = X.shape
    perms = np.array([rng.permutation(n) for _ in range(H)])
    prio = rng.random((H, n))
    cur = conflicts(X, s, perms, prio)
    best = cur
    for it in range(iters):
        if cur == 0:
            return 0, perms, prio
        T = T0 * (T1 / T0) ** (it / iters)
        h = rng.integers(H)
        move = rng.integers(3)
        perms2 = perms.copy(); prio2 = prio.copy()
        if move == 0:  # swap two positions in a perm
            i, j = rng.integers(n), rng.integers(n)
            perms2[h, i], perms2[h, j] = perms2[h, j], perms2[h, i]
        elif move == 1:  # move one coordinate to a new position
            i, j = rng.integers(n), rng.integers(n)
            p = list(perms2[h]); v = p.pop(i); p.insert(j, v); perms2[h] = p
        else:  # change a priority
            k = rng.integers(n)
            prio2[h, k] = rng.random()
        new = conflicts(X, s, perms2, prio2)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            perms, prio, cur = perms2, prio2, new
            best = min(best, cur)
    return best, perms, prio


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=6)
    ap.add_argument("--H", type=int, nargs="+", default=[2, 3, 4, 6, 8])
    ap.add_argument("--funcs", type=int, default=3)
    ap.add_argument("--iters", type=int, default=20000)
    ap.add_argument("--restarts", type=int, default=3)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--parity", action="store_true")
    args = ap.parse_args()
    n = args.n; X = cube_supports(n); N = 2 ** n
    rng = np.random.default_rng(args.seed)
    for fi in range(args.funcs):
        if args.parity:
            s = np.where(X.sum(1) % 2 == 1, 1, -1)
        else:
            s = rng.choice([-1, 1], size=N)
        s[0] = 0  # x = 0 handled by sigma
        for H in args.H:
            t0 = time.time(); best = None
            for r in range(args.restarts):
                b, perms, prio = anneal(X, s, H, iters=args.iters, seed=args.seed * 1000 + fi * 10 + r)
                best = b if best is None else min(best, b)
                if b == 0:
                    break
            print(f"tropical n={n} func={fi} H={H} best_conflicts={best} [{time.time()-t0:.0f}s]", flush=True)
            if best == 0:
                break
        if args.parity:
            break


if __name__ == "__main__":
    main()
