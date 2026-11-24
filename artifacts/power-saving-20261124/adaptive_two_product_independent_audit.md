# Independent audit of the adaptive two-product separation

## Verdict and scope

I independently read `adaptive_two_product_separation.md` and its exact checker, then reran `check_two_head_adaptive_product_separation.py`. The finite certificate and the general rank proof are correct. They give a strict Boolean target on $38$ bits with original head complexity exactly two, which requires at least three arbitrary affine-times-product atoms even when a free bias is allowed.

This is a written proof supported by exact rational computation. It is not Lean kernel verification and does not prove an asymptotic head lower bound. It rules out a same-width compiler at width two, while allowing a compiler with any larger constant factor.

## Checks

**Exact selected table.** The checker uses Python `Fraction` arithmetic, with no numerical optimization. It verifies all $192$ nonzero signs, all $32$ antipodal sign classes on six rows, strictly positive denominators, and the minimum selected absolute value $1/20670$.

**Original-model realization.** The one-hot row and column inputs are genuine vertices of the $38$-bit cube. The displayed affine denominators restrict to the certified additive denominator tables. Their constants are $1/2048$ and $4077/38912$, and every slope is at least $1/4096$. Thus both denominators are strictly positive on the entire cube and have strictly positive coherent slopes. The arbitrary affine numerator coefficients are permitted because the denominators are nonconstant.

**Full-cube strictification.** Every unperturbed cube score is rational. Adding $sqrt2/82680$ makes every score nonzero, including all vertices outside the selected table. This bias is positive and less than $1/41340$, so it preserves the selected signs. The argument proves strictness without enumerating the full cube.

**Sign rank.** For a nonzero left-kernel vector, extend the signs of its nonzero coordinates to a complete sign vector. A column from that antipodal class makes every nonzero summand of its inner product with the kernel vector have the same strict sign. The inner product cannot vanish. Therefore every real matrix with the selected signs has rank six.

**Arbitrary adaptive products.** A product of arbitrary one-bit factors separates into a row factor and a column factor on the selected inputs. Multiplying by an affine form gives the sum of two rank-one matrices. This factorization uses no division, so zero and negative factors cause no exception. Two such atoms and a bias have rank at most five. Their coefficients and factors may depend jointly on the entire target; the rank bound still applies.

**Exact original complexity.** A single original head and a bias have the sign of the affine numerator $A+cB$, since $B$ is positive. An affine table on the selected inputs has rank at most two, so its signs cannot be the certified pattern. The target therefore has original head complexity exactly two.
