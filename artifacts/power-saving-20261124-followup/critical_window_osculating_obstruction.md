# Padding transfers the osculating obstruction to the critical width window

## Status and ingredients

This is a written consequence of three ingredients. It strengthens the scope of the inherited obstruction to a proposed strict osculating compiler. It is not a lower bound for the original unrestricted model.

- Dummy-variable invariance is kernel checked in `formalization/HeadComplexity/Results/DummyVariables.lean`, especially `HeadComplexity.computableWithHeadsN_dummyVariablesAlong_iff` and `HeadComplexity.HStar_dummyVariables`. The construction uses small positive dummy weights and preserves every label at exactly the same width.
- The written weighted count in `artifacts/power-saving-20261124/curvilinear_osculating_capacity.md` gives, with $p=2(n+1)m\leq2^n$, at most $(16e^2 2^n/p)^p$ strict sign tables of osculating length at most $m$. Allowing shorter lengths causes no problem because a shorter denominator jet and numerator jet can be padded with zeros.
- The prior original-model upper theorem gives $W(n)\leq K2^n/(n\log n)$ for $n\geq32$, with $K=2323202$. Its exact source and saved standard-axiom transcript are documented in `artifacts/power-saving-20261124/prior_universal_log_upper_provenance.md`. That theorem has not been freshly rebuilt in this run. The consequence below takes that prior theorem as established, with precisely this provenance qualification.

The weighted count remains a written proof, rather than a Lean declaration. The present consequence therefore has the same written status even though dummy-variable invariance is formalized.

## Restriction preserves strict osculating length

Fix any coordinates of an osculating representation. Every denominator jet and numerator coefficient remains affine in the remaining variables. Positivity of the base denominator is preserved. Formal reciprocal coefficient extraction commutes with this substitution. Thus the restricted score is an osculating representation of the same or smaller length, with all nonzero score signs retained.

This is essential: after using a compiler in a slightly larger dimension, the capacity count will be applied on the original smaller cube, which has fewer parameter coefficients and fewer truth-table coordinates.

## Critical-only compilers are also obstructed

Fix $c\gt0$. Consider either critical width budget

$$ h_\ast(d)=\left\lfloor c\frac{2^d}{d^{3/2}}\right\rfloor,\qquad\text{or}\qquad h_\ast(d)=\left\lfloor c\frac{2^d\log d}{d^2}\right\rfloor. $$

Suppose a proposed theorem applies only at this exact width. Let $g$ and $a$ be nonnegative functions. Assume that every truth table representable by $h_\ast(d)$ original heads admits a strict osculating representation of length at most

$$ g(d)h_\ast(d)+a(d),\qquad g(d)=o(\log d),\qquad a(d)=\exp(o(d)). $$

Then the proposed theorem contradicts the three ingredients above. In particular, even restricting the claim to the critical window does not permit a constant-factor strict osculating compiler with an additive subexponential number of terms.

**Proof.** Put $U(n)=\lceil K2^n/(n\log n)\rceil$. Every $n$-bit truth table is representable with $U(n)$ heads, using ordinary width monotonicity after the prior upper theorem.

Choose the least integer $d\geq n$ for which $h_\ast(d)\geq U(n)$. For both displayed budgets, their ratio to $U(n)$ at $d=n$ tends to zero. Increasing $d$ by $O(\log n)$ multiplies the exponential factor by a sufficiently large polynomial while changing the polynomial denominator by only $1+o(1)$. Hence the least such dimension satisfies

$$ d=n+O(\log n),\qquad U(n)\leq h_\ast(d)\leq3U(n) $$

for all sufficiently large $n$. The factor three follows from minimality and the adjacent-budget ratio: before taking floors, that ratio tends to two; the floor and ceiling errors are negligible because $U(n)\to\infty$. This also handles a compiler promised only at the exact width $h_\ast(d)$, rather than at every smaller width.

Extend every $n$-bit target by $d-n$ dummy variables. Dummy-variable invariance and width monotonicity make it representable at the precise width $h_\ast(d)$. Apply the proposed compiler, and then restrict the dummy variables. Every original target would have strict osculating length at most

$$ m_n=3g(d)U(n)+a(d)=o(2^n/n). $$

Here $d/n\to1$, $\log d/\log n\to1$, and $a(d)=\exp(o(n))=o(2^n/n)$. Integer rounding adds only one and does not alter the estimate.

Set $p_n=2(n+1)(\lceil m_n\rceil+1)$. This harmless padding ensures $p_n\gt0$. Then $p_n/2^n\to0$, and the weighted count has base-two logarithm at most

$$ p_n\log_2\left(\frac{16e^2 2^n}{p_n}\right)=o(2^n), $$

because $r\log(1/r)\to0$ as $r\downarrow0$. It cannot contain all $2^{2^n}$ truth tables. This is the contradiction. $\blacksquare$

## Remaining possible access theorem

This obstruction does not exclude an overhead of order $\log n$ or larger. Such an overhead is still small enough to be useful: an osculating compiler of width $O(H\log n)+\exp(o(n))$, combined with the inherited weighted count, would yield an unrestricted lower bound of order $2^n/(n\log n)$ after sufficiently small constants are chosen.

It also does not exclude the requested constant-overhead relative-margin repair. That target class has a different capacity formula, with a margin-dependent degree cost. Nor does it exclude the free affine-product compiler under investigation; its ordinary degree is proportional to the input dimension, and its finite count is different.

The point of the padding argument is a quantifier correction. Restricting a compiler claim to near-critical exponential widths does not by itself evade a known obstruction for a class closed under coordinate restriction. The actual output width and the capacity of the restricted target class must still be checked.
