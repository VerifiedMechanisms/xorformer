"""Exact single-layer spectral-factor sign and real-root certificates.

No recursive compiler or HeadComplexity asymptotic is asserted.
"""
from fractions import Fraction as Q
from itertools import product


def add(a, b):
    return [(a[k] if k < len(a) else Q(0)) +
            (b[k] if k < len(b) else Q(0))
            for k in range(max(len(a), len(b)))]


def scale(a, c):
    return [c*x for x in a]


def mul(a, b):
    out = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def deriv(a):
    return [k*a[k] for k in range(1, len(a))] or [Q(0)]


def ev(a, t):
    out = Q(0)
    for x in reversed(a):
        out = out*t+x
    return out


def complex_product(centers, signs, eta):
    re, im = [Q(1)], [Q(0)]
    for t, s in zip(centers, signs):
        re, im = (add(mul(re, [-t, Q(1)]), scale(im, -s*eta)),
                  add(mul(im, [-t, Q(1)]), scale(re, s*eta)))
    # C=(1+i)Z. Its real and imaginary leading coefficients both equal one.
    return add(re, scale(im, -1)), add(re, im)


def check_degree(d):
    centers = [Q(j+1) for j in range(d)]
    eta = Q(1, 100*d*d)
    m = d+1
    poles = [Q(j+1, 100*m) for j in range(m)]
    rad = Q(1, 400*m)
    endpoints = [p+s*rad for p in poles for s in (-1, 1)]
    u = [Q(1)]
    for p in poles:
        u = mul(u, [-p, Q(1)])
    p = mul(u, u)
    dp = deriv(p)
    norm = [Q(2)]
    for center in centers:
        norm = mul(norm, [center*center+eta*eta, -2*center, Q(1)])
    count = 0
    for signs in product((-1, 1), repeat=d):
        a, b = complex_product(centers, signs, eta)
        aa, bb = mul(a, a), mul(b, b)
        r = add(aa, scale(bb, -1))
        dr = deriv(r)
        assert r[-1] == 0
        assert add(aa, bb) == norm
        for sigma, center in zip(signs, centers):
            assert -sigma*ev(r, center+eta) > 0
            numerator = ev(dr, center)*ev(p, center)-ev(r, center)*ev(dp, center)
            assert -sigma*numerator > 0
        # Isolating endpoint certificates for all four real-rooted children.
        delta = min(abs(ev(u, t))/(1+abs(ev(a, t))+abs(ev(b, t)))
                    for t in endpoints)/2
        assert delta > 0
        while True:
            ga = add(p, scale(aa, -delta*delta))
            gb = add(p, scale(bb, -delta*delta))
            dga, dgb = deriv(ga), deriv(gb)
            if all(s*(ev(dga,t)/ev(ga,t)-ev(dgb,t)/ev(gb,t)) > 0
                   for s,t in zip(signs, centers)):
                break
            delta /= 2
        children = [add(u, scale(v, s*delta)) for v in (a,b) for s in (-1,1)]
        for child in children:
            assert child[-1] == 1
            for i in range(m):
                lo, hi = endpoints[2*i:2*i+2]
                assert ev(child, lo)*ev(child, hi) < 0
        assert mul(children[0],children[1]) == ga
        assert mul(children[2],children[3]) == gb
        mean = add(p, scale(norm, -delta*delta/2))
        assert add(ga,gb) == scale(mean,2)
        for sigma,t in zip(signs,centers):
            numerator = ev(dr,t)*ev(mean,t)-ev(r,t)*ev(deriv(mean),t)
            difference = ev(dga,t)/ev(ga,t)-ev(dgb,t)/ev(gb,t)
            assert difference == -delta*delta*numerator/(ev(ga,t)*ev(gb,t))
            assert sigma*difference > 0
        count += 1
    print(f'D={d}: {count} complete rational spectral and four-child certificates', flush=True)
    return count


if __name__ == '__main__':
    count = sum(check_degree(d) for d in range(1, 9))
    assert count == 510
    print(f'All {count} exact certificates passed. No recursive coverage tested.')
