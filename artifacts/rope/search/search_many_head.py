"""Explore same-head Boolean fits, with independent exact integer certificates.

Run resource-intensive searches as `heavy python3 ...`. Numerical failure is an
unresolved optimization instance, never a lower-bound or separation certificate.
The verifier itself uses only Python integers and checks every cube vertex.
"""
import argparse
import json
import math
from pathlib import Path
import time


def verify(record):
    n, heads = record["n"], record["heads"]
    p = record["pure_certificate"]
    q = record["vanilla_integer_certificate"]
    assert len(p["a"]) == len(p["b"]) == len(p["gamma"]) == len(p["values"]) == heads
    assert all(len(row) == n for row in p["a"] + p["b"])
    assert all(v > 0 for row in p["a"] + p["b"] for v in row)
    assert all(v > 0 for v in p["gamma"])
    assert all(len(row) == 3 for row in p["values"])
    assert len(q["denominators"]) == len(q["numerators"]) == heads
    for d in q["denominators"]:
        assert len(d) == n + 1 and d[0] > sum(abs(v) for v in d[1:])
        assert all(v > 0 for v in d[1:]) or all(v < 0 for v in d[1:])
    assert all(len(a) == n + 1 for a in q["numerators"])
    integer_rows = p["a"] + p["b"] + p["values"] + q["denominators"] + q["numerators"]
    assert all(type(v) is int for row in integer_rows for v in row)
    assert all(type(v) is int for v in p["gamma"] + p["constant"])
    cnum, cden = p["constant"]
    assert cden > 0
    truth = int(p["truth_table"], 16)
    margin = None
    for mask in range(1 << n):
        x = [(mask >> i) & 1 for i in range(n)]
        z = [1] + [2 * v - 1 for v in x]
        pd, pn = [], []
        for h in range(heads):
            v0, v1, vq = p["values"][h]
            pd.append(p["gamma"][h] + sum(p["b"][h][i] if x[i] else p["a"][h][i] for i in range(n)))
            pn.append(p["gamma"][h] * vq + sum(p["b"][h][i] * v1 if x[i] else p["a"][h][i] * v0 for i in range(n)))
        pure = cnum * math.prod(pd) + cden * sum(pn[h] * math.prod(pd[j] for j in range(heads) if j != h) for h in range(heads))
        vd = [sum(a * b for a, b in zip(d, z)) for d in q["denominators"]]
        vn = [sum(a * b for a, b in zip(a, z)) for a in q["numerators"]]
        vanilla = sum(vn[h] * math.prod(vd[j] for j in range(heads) if j != h) for h in range(heads))
        sign = 1 if (truth >> mask) & 1 else -1
        assert min(vd) > 0 and sign * pure > 0 and sign * vanilla > 0, (record["sample"], mask)
        margin = sign * vanilla if margin is None else min(margin, sign * vanilla)
    return margin


def vertices(n):
    import numpy as np
    return np.array([[2 * ((k >> i) & 1) - 1 for i in range(n)] for k in range(1 << n)], float)


def generate(Z, rng, heads, mode, spread=0):
    import numpy as np
    from scipy.linalg import eigh
    n = Z.shape[1]
    X = ((Z + 1) / 2).astype(int)
    a = rng.integers(1, 100, (heads, n)) if not spread else np.rint(np.exp(rng.uniform(0, spread, (heads, n)))).astype(int)
    b = rng.integers(1, 100, (heads, n)) if not spread else np.rint(np.exp(rng.uniform(0, spread, (heads, n)))).astype(int)
    gamma = rng.integers(1, 100 if not spread else 10, heads)
    if mode in ("reciprocal", "flipped_reciprocal", "grid_reciprocal"):
        # The basic reciprocal mode has zero-sum centered slopes. The flipped
        # mode complements a common subset of coordinates of oriented forms.
        # The grid mode repeats three block directions. These are route probes.
        mask = rng.choice([-1, 1], n) if mode != "reciprocal" else None
        if mask is not None:
            mask[0], mask[-1] = 1, -1
        for h in range(heads):
            if mode == "flipped_reciprocal":
                slopes = rng.integers(1, 1000, n) * mask
            elif mode == "grid_reciprocal":
                directions = rng.integers(-1000, 1001, 3)
                slopes = np.array([directions[i % 3] for i in range(n)])
            else:
                slopes = rng.integers(1, 1000, n // 2)
                slopes = np.concatenate([slopes, -slopes, np.zeros(n % 2, int)])
                rng.shuffle(slopes)
            a[h] = 1 + np.maximum(-slopes, 0)
            b[h] = 1 + np.maximum(slopes, 0)
        values = np.zeros((heads, 3), int)
        values[:, 2] = rng.integers(1, 1000, heads) * rng.choice([-1, 1], heads)
        N = np.tile(gamma * values[:, 2], (len(X), 1))
        D = gamma + (1 - X) @ a.T + X @ b.T
        cden = 1000000000
        cnum = -round(float(np.quantile((N / D).sum(axis=1), rng.uniform(0.2, 0.8))) * cden)
    elif mode != "random" and not spread and rng.random() < 0.5:
        for h in range(1, heads):
            a[h] = np.maximum(1, a[0] + rng.integers(-20, 21, n))
            b[h] = np.maximum(1, b[0] + rng.integers(-20, 21, n))
    D = gamma + (1 - X) @ a.T + X @ b.T
    if mode in ("reciprocal", "flipped_reciprocal", "grid_reciprocal"):
        pass
    elif mode == "random":
        values = rng.integers(-10, 11, (heads, 3))
        N = gamma * values[:, 2] + (1 - X) @ (a * values[:, 0, None]).T + X @ (b * values[:, 1, None]).T
        cden = 1000000
        cnum = -round(float(np.quantile((N / D).sum(axis=1), rng.uniform(0.2, 0.8))) * cden)
    else:
        F = np.column_stack([(X @ b[h]) / D[:, h] for h in range(heads)] + [gamma[h] / D[:, h] for h in range(heads)])
        means = F.mean(axis=0)
        F0 = F - means
        low = Z if mode == "linear" else np.column_stack([Z] + [Z[:, i] * Z[:, j] for i in range(n) for j in range(i)])
        L = low.T @ F0 / len(Z)
        G = F0.T @ F0 / len(Z)
        _, vec = eigh(L.T @ L, G + 1e-13 * np.eye(2 * heads))
        coeff = vec[:, 0]
        coeff = np.rint(coeff / np.max(abs(coeff)) * 1000000).astype(int)
        values = np.column_stack([np.zeros(heads, int), coeff[:heads], coeff[heads:]])
        N = gamma * values[:, 2] + X @ (b * values[:, 1, None]).T
        cden = 2
        cnum = -round(float(means @ coeff) * cden) + 1
    # Object arrays prevent overflow in the exact cleared numerator.
    Do, No = D.astype(object), N.astype(object)
    P = cnum * np.prod(Do, axis=1)
    for h in range(heads):
        P += cden * No[:, h] * np.prod(np.delete(Do, h, axis=1), axis=1)
    if any(v == 0 for v in P):
        return generate(Z, rng, heads, mode, spread)
    y = np.array([1.0 if v > 0 else -1.0 for v in P])
    return y, {"a": a.tolist(), "b": b.tolist(), "gamma": gamma.tolist(), "values": values.tolist(), "constant": [cnum, cden], "truth_table": hex(sum(int(v > 0) << i for i, v in enumerate(P))), "minimum_cleared_margin": int(min(abs(v) for v in P))}


def endpoint_biases(p):
    """Positive uniformly oriented endpoint forms from the proved pure lemma."""
    import numpy as np
    answer = []
    for h, (v0, v1, vq) in enumerate(p["values"]):
        delta = v1 - v0
        if delta == 0:
            answer.append(np.full(len(p["a"][h]), 0.25 / len(p["a"][h])))
            continue
        if delta * (vq - v0) > 0:
            slopes = abs(delta) * np.array(p["b"][h], float)
            constant = abs(vq - v0) * p["gamma"][h]
        else:
            slopes = -abs(delta) * np.array(p["a"][h], float)
            constant = abs(v1 - vq) * p["gamma"][h] - slopes.sum()
        center = constant + slopes.sum() / 2
        beta = slopes / (2 * center)
        assert abs(beta).sum() < 1
        answer.append(beta)
    return np.array(answer)


def fit(Z, y, heads, restarts, rng, maxiter, pure=None):
    import numpy as np
    from scipy.optimize import linprog, minimize
    X = np.column_stack([np.ones(len(Z)), Z])
    n = Z.shape[1]
    size = heads * (n + 1)
    best = float("inf")
    for restart in range(restarts):
        signs = np.array([-1.0 if h < restart % (heads + 1) else 1.0 for h in range(heads)])
        seeded = pure is not None
        if seeded:
            initial_B = endpoint_biases(pure)
            if restart % (heads + 2) == 0:
                signs = np.sign(initial_B[:, 0])
            initial_B = signs[:, None] * abs(initial_B)

        def objective(theta):
            L = theta[:size].reshape(heads, n + 1)
            W = np.exp(L - L.max(axis=1, keepdims=True))
            W /= W.sum(axis=1, keepdims=True)
            B = signs[:, None] * W[:, 1:]
            D = 1 + Z @ B.T
            A = theta[size:].reshape(heads, n + 1)
            N = X @ A.T
            cof = np.column_stack([np.prod(np.delete(D, h, axis=1), axis=1) for h in range(heads)])
            P = np.sum(N * cof, axis=1)
            gap = np.minimum(y * P - 1, 0)
            gp = 2 * gap * y / len(y)
            reg = 1e-10
            gA = (X.T @ (gp[:, None] * cof)).T + 2 * reg * A
            gB = np.zeros((heads, n))
            for h in range(heads):
                dP = sum(N[:, j] * np.prod(np.delete(D, [h, j], axis=1), axis=1) for j in range(heads) if j != h)
                gB[h] = Z.T @ (gp * dP)
            gW = np.column_stack([np.zeros(heads), signs[:, None] * gB])
            gL = W * (gW - np.sum(gW * W, axis=1, keepdims=True))
            return np.mean(gap ** 2) + reg * np.sum(A ** 2), np.concatenate([gL.ravel(), gA.ravel()])

        theta = rng.normal(size=2 * size)
        theta[:size] *= 2
        if seeded:
            weights = np.column_stack([1 - abs(initial_B).sum(axis=1), abs(initial_B)])
            initial_L = np.log(weights)
            if restart >= heads + 2:
                initial_L += rng.normal(size=initial_L.shape) * (0.5 if restart % 2 else 1.5)
            theta[:size] = initial_L.ravel()
            weights = np.exp(initial_L - initial_L.max(axis=1, keepdims=True))
            weights /= weights.sum(axis=1, keepdims=True)
            initial_D = 1 + Z @ (signs[:, None] * weights[:, 1:]).T
            initial_F = np.column_stack([X * np.prod(np.delete(initial_D, h, axis=1), axis=1)[:, None] for h in range(heads)])
            theta[size:] = np.linalg.lstsq(initial_F, y, rcond=1e-12)[0]
        result = minimize(objective, theta, jac=True, method="L-BFGS-B", options={"maxiter": maxiter, "ftol": 1e-13, "gtol": 1e-8})
        best = min(best, result.fun)
        L = result.x[:size].reshape(heads, n + 1)
        W = np.exp(L - L.max(axis=1, keepdims=True))
        W /= W.sum(axis=1, keepdims=True)
        B = signs[:, None] * W[:, 1:]
        D = 1 + Z @ B.T
        F = np.column_stack([X * np.prod(np.delete(D, h, axis=1), axis=1)[:, None] for h in range(heads)])
        lp = linprog(np.zeros(size), A_ub=-y[:, None] * F, b_ub=-np.ones(len(y)), bounds=[(None, None)] * size, method="highs")
        if lp.success and np.min(y * (F @ lp.x)) > 0.9:
            return {"status": "floating_fit", "restarts": restart + 1, "loss": float(best), "B": B.tolist()}
    return {"status": "unresolved", "restarts": restarts, "loss": float(best)}


def rationalize(record, Z, y):
    import numpy as np
    from scipy.optimize import linprog
    n, heads = record["n"], record["heads"]
    X = np.column_stack([np.ones(len(Z)), Z])
    B = record["vanilla_search"]["B"]
    for scale in (10 ** 6, 10 ** 9, 10 ** 12):
        denominators = []
        for b in B:
            slopes = [(1 if v > 0 else -1) * max(1, round(abs(v) * scale)) for v in b]
            gap = max(1, round((1 - sum(abs(v) for v in b)) * scale))
            denominators.append([sum(abs(v) for v in slopes) + gap] + slopes)
        D = X @ np.array(denominators, float).T / scale
        F = np.column_stack([X * np.prod(np.delete(D, h, axis=1), axis=1)[:, None] for h in range(heads)])
        # Work in an orthonormal basis of the same numerical feature space.
        # The exact verifier below remains the authority if a nearly singular
        # feature direction is lost or floating linear algebra is inaccurate.
        u, singular, v = np.linalg.svd(F, full_matrices=False)
        rank = int(np.sum(singular > 1e-13 * singular[0]))
        lp = linprog(np.zeros(rank), A_ub=-y[:, None] * u[:, :rank], b_ub=-np.ones(len(y)), bounds=[(None, None)] * rank, method="highs")
        if not lp.success:
            continue
        coefficients = v[:rank].T @ (lp.x / singular[:rank])
        for numscale in (10 ** 6, 10 ** 9, 10 ** 12):
            numerators = [[int(round(v * numscale)) for v in row] for row in coefficients.reshape(heads, n + 1)]
            candidate = {key: record[key] for key in ("sample", "n", "heads", "mode", "pure_certificate")}
            candidate["vanilla_integer_certificate"] = {"denominators": denominators, "numerators": numerators}
            try:
                candidate["minimum_integer_margin"] = verify(candidate)
            except AssertionError:
                continue
            return candidate
    return None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--verify", nargs="+")
    parser.add_argument("--retry")
    parser.add_argument("--n", type=int, default=8)
    parser.add_argument("--heads", type=int, default=3)
    parser.add_argument("--samples", type=int, default=30)
    parser.add_argument("--restarts", type=int, default=12)
    parser.add_argument("--maxiter", type=int, default=2000)
    parser.add_argument("--mode", choices=("random", "linear", "quadratic", "reciprocal", "flipped_reciprocal", "grid_reciprocal"), default="quadratic")
    parser.add_argument("--spread", type=float, default=0)
    parser.add_argument("--seed", type=int, default=2026112422)
    args = parser.parse_args()
    if args.verify:
        count = 0
        for path in args.verify:
            for line in Path(path).read_text().splitlines():
                verify(json.loads(line))
                count += 1
        print(f"Verified {count} exact same-head certificates with integer arithmetic.")
        return
    import numpy as np
    rng = np.random.default_rng(args.seed)
    if args.retry:
        records = [json.loads(line) for line in Path(args.retry).read_text().splitlines()]
        output = Path(args.retry).with_suffix(".retry.exact.jsonl")
        for record in records:
            if record["vanilla_search"]["status"] != "unresolved":
                continue
            Z = vertices(record["n"])
            truth = int(record["pure_certificate"]["truth_table"], 16)
            y = np.array([1.0 if (truth >> i) & 1 else -1.0 for i in range(1 << record["n"])])
            start = time.monotonic()
            record["vanilla_search"] = fit(Z, y, record["heads"], args.restarts, rng, args.maxiter, record["pure_certificate"])
            exact = rationalize(record, Z, y) if record["vanilla_search"]["status"] == "floating_fit" else None
            if exact:
                with output.open("a") as file:
                    file.write(json.dumps(exact, separators=(",", ":")) + "\n")
            print(record["sample"], record["vanilla_search"]["status"], "exact" if exact else "uncertified", record["vanilla_search"]["restarts"], round(time.monotonic() - start, 2), flush=True)
        return
    Z = vertices(args.n)
    prefix = Path(__file__).parent / f"many_h{args.heads}_n{args.n}_{args.mode}_{args.seed}"
    for sample in range(args.samples):
        start = time.monotonic()
        y, pure = generate(Z, rng, args.heads, args.mode, args.spread)
        result = fit(Z, y, args.heads, args.restarts, rng, args.maxiter)
        record = {"sample": sample, "n": args.n, "heads": args.heads, "mode": args.mode, "configuration": {"seed": args.seed, "spread": args.spread, "restarts": args.restarts, "maxiter": args.maxiter}, "pure_certificate": pure, "vanilla_search": result}
        exact = rationalize(record, Z, y) if result["status"] == "floating_fit" else None
        record["seconds"] = time.monotonic() - start
        with prefix.with_suffix(".jsonl").open("a") as file:
            file.write(json.dumps(record) + "\n")
        if exact:
            with prefix.with_suffix(".exact.jsonl").open("a") as file:
                file.write(json.dumps(exact, separators=(",", ":")) + "\n")
        print(sample, result["status"], "exact" if exact else "uncertified", result["restarts"], round(result["loss"], 8), round(record["seconds"], 2), flush=True)


if __name__ == "__main__":
    main()
