# A Linear Cost Obstruction for a Single Quadratic Jet

## Statement

**Theorem.** For every integer $k\geq24$, there is a quadratic polynomial $Q$ on $n=3k$ Boolean variables such that the predicate $Q\gt0$ requires more than $n/72$ heads in the unchanged attention model. Consequently, an arbitrary linear combination of second-order reciprocal jets at a single fixed positive affine denominator cannot be compiled into a bounded number of actual heads.

This is an obstruction to a proposed compiler, not a proof of the research target. A lower bound linear in $n$ is far below the selected exponential scale. The theorem does not imply that costs add across multiple jet centers.

## An explicit family with cubic entropy

Split the input into three blocks $x,y,z\in\lbrace0,1\rbrace^k$, and define the integer address

$$ I(x)=\sum_{i=0}^{k-1}2^i x_i. $$

Choose an arbitrary matrix $T=(t_{j\ell})$ with $k^2$ entries in $\lbrace0,\ldots,2^k-1\rbrace$. Define

$$ Q_T(x,y,z)=I(x)\sum_{\ell=1}^k z_\ell-\sum_{j=1}^k\sum_{\ell=1}^k t_{j\ell}y_jz_\ell. $$

This is a polynomial of degree at most two. At the one-hot selectors $y=e_j$ and $z=e_\ell$, it satisfies

$$ Q_T(x,e_j,e_\ell)=I(x)-t_{j\ell}. $$

Thus the Boolean function $f_T=\mathbf1[Q_T\gt0]$ determines every matrix entry. Indeed, if $t_{j\ell}\lt u_{j\ell}$, choose the unique address $x$ with $I(x)=u_{j\ell}$. Then $Q_T(x,e_j,e_\ell)\gt0$ while $Q_U(x,e_j,e_\ell)=0$. The two Boolean functions differ. Reversing the two matrices covers the other inequality.

There are therefore exactly

$$ (2^k)^{k^2}=2^{k^3} $$

distinct functions in this family. If strict signs at every cube vertex are preferred, replace every $Q_T$ by $Q_T-1/2$. All original values are integers, so this preserves every label and eliminates all zeros. The degree remains at most two.

## Counting all admissible head representations

The normalized counting proof in `version-5.tex`, equation `normalized-sign-count`, applies to every admissible representation, including target-dependent denominators. If $H\geq1$ and $2nH\leq2^n-1$, it gives

$$ \lvert\lbrace f:H^{\ast}(f)\leq H\rbrace\rvert\leq2\left(\frac{2e(2^n-1)}{n}\right)^{2nH}. $$

For clarity, the score is strictified and normalized to a discrete constant sign plus $2nH$ real parameters. Clearing the positive denominators at the nonzero cube inputs produces polynomials of parameter degree $H$. Warren's strict-sign bound then gives the displayed inequality. The analytic bound is also stated as Theorem 2.1 in [Goldberg and Jerrum](https://www.cs.ox.ac.uk/people/paul.goldberg/papers/goldbergjerrum.pdf). No restriction on coefficient heights, margins, or denominator dependence is introduced.

Set $n=3k$ and $H=\lfloor k/24\rfloor$. Then $H\geq1$. The required sample-size condition holds: using $k\leq2^k$ gives

$$ 2nH\leq\frac{k^2}{4}\leq\frac{4^k}{4}\lt8^k-1=2^n-1. $$

Since $e\lt3$ and $n\geq3$, the base in the sign count is less than $2^{n+1}$. Hence

$$ \lvert\lbrace f:H^{\ast}(f)\leq H\rbrace\rvert\lt2^{1+2nH(n+1)}\leq2^{1+(3/4)k^3+(1/4)k^2}\lt2^{k^3}. $$

The final strict inequality follows from $k^2(k-1)\gt4$, which holds for $k\geq3$. Comparison with the injective family proves that some $f_T$ requires more than $\lfloor k/24\rfloor$ heads. Since head counts are integers, its complexity is strictly greater than $k/24=n/72$. This proves the head lower bound. $\blacksquare$

## Why this concerns a single jet center

Fix the affine denominator $B(x,y,z)=1+\sum_i x_i+\sum_j y_j+\sum_\ell z_\ell$. Every coefficient is strictly positive. The signs of $Q_T/B^3$ and $Q_T$ agree on every cube vertex. For the reciprocal map $b\mapsto1/(b_0+\sum_i b_i u_i)$, setting $u_0=1$ gives

$$ \frac{\partial^2}{\partial b_i\partial b_j}\frac{1}{b_0+\sum_a b_a u_a}=\frac{2u_i u_j}{(b_0+\sum_a b_a u_a)^3}. $$

Every quadratic numerator, including its constant and linear terms, is a linear combination of these second derivatives at the single point $b_0=b_1=\cdots=b_n=1$. Thus the lower bound applies even to one fixed jet center. It rules out a uniform constant cost for compiling arbitrary quadratic jet combinations, including compilation that may choose entirely different target-dependent denominators.

This does not prove a direct-sum theorem across the centers in the open-code interpolation construction. Such an assertion would be a separate substantive theorem, and none is established here.

## Formal boundary

`formalization/HeadComplexity/Atoms/QuadraticThresholdEncoding.lean` defines the quadratic family on three Boolean blocks. `score_units` proves the one-hot evaluation identity; `family_injective` and `family_card` prove the exact count $2^{k^3}$. `exists_outside` supplies the finite counting consequence, and `head_count_exponent_lt` checks the relevant integer exponent inequality. The identification with second derivatives and the application of Warren's analytic theorem are the written proofs above. No new Lean declaration is claimed to prove Warren's theorem or the main asymptotic target.
