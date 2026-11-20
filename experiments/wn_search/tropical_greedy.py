"""Greedy constructor for the tropical (dominance) sub-model on random targets.

Random orders pi_h; priorities assigned greedily: repeatedly use an unused rule whose uncaught part is
nonempty and monochromatic, preferring the largest uncaught part. If it finishes, we have a valid tropical
representation (hence H*(f) <= H by the transfer theorem). We binary-search the smallest H (over a few
order samples) for which the greedy finishes, and report H n^2/N and H n/N.
"""
import argparse, numpy as np, time


def run_greedy(n, H, f, rng):
    N = 2 ** n
    # supports
    xs = np.arange(1, N)
    bits = ((xs[:, None] >> np.arange(n)[None, :]) & 1).astype(bool)  # (N-1) x n
    perms = [rng.permutation(n) for _ in range(H)]
    # rule index of each point in each head: k = min position of support
    rule_of = np.zeros((N - 1, H), dtype=np.int64)
    for h in range(H):
        pos = np.empty(n, dtype=np.int64); pos[perms[h]] = np.arange(n)
        P = np.where(bits, pos[None, :], n)
        rule_of[:, h] = h * n + P.min(1)
    R = n * H
    # members of each rule
    members = [[] for _ in range(R)]
    for idx in range(N - 1):
        for h in range(H):
            members[rule_of[idx, h]].append(idx)
    members = [np.array(m, dtype=np.int64) for m in members]
    cnt_p = np.zeros(R, dtype=np.int64); cnt_m = np.zeros(R, dtype=np.int64)
    for r in range(R):
        if members[r].size:
            cnt_p[r] = int((f[members[r]] > 0).sum()); cnt_m[r] = members[r].size - cnt_p[r]
    caught = np.zeros(N - 1, dtype=bool)
    used = np.zeros(R, dtype=bool)
    order = []
    ncaught = 0
    while ncaught < N - 1:
        tot = cnt_p + cnt_m
        mono = (~used) & (tot > 0) & ((cnt_p == 0) | (cnt_m == 0))
        if not mono.any():
            return False, ncaught / (N - 1), len(order)
        cand = np.where(mono)[0]
        r = cand[np.argmax(tot[cand])]
        used[r] = True; order.append(r)
        pts = members[r][~caught[members[r]]]
        caught[pts] = True; ncaught += pts.size
        # update counts in all rules containing these points
        for idx in pts:
            for h in range(H):
                rr = rule_of[idx, h]
                if f[idx] > 0: cnt_p[rr] -= 1
                else: cnt_m[rr] -= 1
    return True, 1.0, len(order)


def min_H(n, f, rng, tries=2, Hmax=None):
    N = 2 ** n
    if Hmax is None: Hmax = N
    lo, hi = 1, Hmax
    # exponential search for a success
    H = 1
    while True:
        ok = any(run_greedy(n, H, f, rng)[0] for _ in range(tries))
        if ok: hi = H; break
        lo = H + 1; H *= 2
        if H > Hmax: return None
    while lo < hi:
        mid = (lo + hi) // 2
        ok = any(run_greedy(n, mid, f, rng)[0] for _ in range(tries))
        if ok: hi = mid
        else: lo = mid + 1
    return hi


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, nargs="+", default=[6, 7, 8, 9, 10])
    ap.add_argument("--funcs", type=int, default=3)
    ap.add_argument("--tries", type=int, default=2)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    for n in args.n:
        N = 2 ** n
        vals = []
        t0 = time.time()
        for fi in range(args.funcs):
            f = rng.choice([-1, 1], size=N - 1)
            Hm = min_H(n, f, rng, tries=args.tries)
            if Hm is None:
                print(f"n={n} func={fi} greedy failed up to Hmax", flush=True); continue
            vals.append(Hm)
            print(f"n={n} func={fi} greedy_min_H={Hm}  H*n^2/N={Hm*n*n/N:.2f}  H*n/N={Hm*n/N:.3f} [{time.time()-t0:.0f}s]", flush=True)
        if vals: print(f"n={n} mean greedy H = {np.mean(vals):.2f}; N/n^2={N/n/n:.2f}; N/n={N/n:.1f}", flush=True)


if __name__ == "__main__":
    main()
