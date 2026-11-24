# An Explicit Gap for the Three-Head Tensor Obstruction

This strengthens the tensor step of [Theorem 22](../../../theorems/03_rotary_attention/022_pure_rope_three_head_separation.md). It is a mathematical estimate, not a Lean theorem and not a numerical bound on the first separating replication count.

## Statement

Let $T$ be the six-by-six-by-six coefficient tensor of the source cubic, retaining one coordinate from each of its three blocks. Let $T'$ be any tensor arising in the same way from three vanilla affine fractions after clearing denominators, including arbitrary affine numerators and a free constant. Then

$$ \max_{a,b,c}|T'_{abc}-T_{abc}|\gt10^{-10}. $$

The denominators may have arbitrarily large or small coefficients. Only their original uniform strict slope signs, or their being constant, are used.

## Coordinate bounds

In one six-coordinate block, the source coordinate change is

$$ d_i=x_i-x_{i+3},\qquad u_i=2\left(\sum_{j=1}^{6}x_j+x_i\right),\qquad i=1,2,3. $$

Write this map as $L$. Its inverse is explicit. With $s=(\sum_i u_i-\sum_i d_i)/7$,

$$ x_i=u_i/2-s,\qquad x_{i+3}=u_i/2-s-d_i. $$

Each denominator-coordinate column of $L^{-1}$ has absolute column sum $11/7$; each numerator-coordinate column has absolute column sum $9/7$. Both are less than two. For a unit Euclidean vector $w$ in the original block, every $d_i(w)$ has absolute value at most $\sqrt2$, and every $u_i(w)$ has absolute value at most six.

Suppose for contradiction that the entrywise tensor difference is at most $\delta=10^{-10}$. Contract both tensors against such a unit $w$. Every entry of the resulting matrix difference is at most $\sqrt6\delta$, by Cauchy-Schwarz. Transform its two matrix modes by $L^{-1}$. The entrywise difference between the transformed contractions is at most

$$ 4\sqrt6\delta\lt10\delta. $$

The source transformed contraction is the matrix $M(d(w),u(w))$ in Theorem 22. Every entry has absolute value at most six. Every entry of the transformed $T'$ contraction therefore has absolute value at most seven.

## From low rank to a nearly paired kernel

The source tensor has a nonzero integer coefficient, so $T'$ is nonzero under the assumed distance bound. At least one of its vanilla denominators is nonconstant. Choose an orthonormal triple $w_1,w_2,w_3$ in the common first-block denominator kernel, and let $W$ be their span. Every contracted $T'$ matrix has rank at most three.

The three selected four-by-four source minors have determinants $d_i(w_j)^4$. The matching $T'$ minors have determinant zero. In a four-by-four determinant, there are 24 permutation products. Telescoping each product difference into four terms, using entry bounds seven and difference bound $10\delta$, gives

$$ |d_i(w_j)|^4\leq24\cdot4\cdot7^3\cdot10\delta\lt400000\delta. $$

Set $\varepsilon=(400000\delta)^{1/4}$. Thus every $|d_i(w_j)|\leq\varepsilon$.

Let $K$ be the source denominator kernel, consisting of paired vectors $(a,b,c,a,b,c)$, and let $P_K,P_W$ be the Euclidean orthogonal projections. The three source denominator rows are orthogonal and have squared norm two, so

$$ \|P_{K^\perp}w_j\|_2^2=\frac12\sum_{i=1}^{3}d_i(w_j)^2\leq\frac32\varepsilon^2. $$

Both projections have rank three. The standard trace identity for orthogonal projections therefore gives

$$ \|P_K-P_W\|_F^2=2\sum_{j=1}^{3}\|P_{K^\perp}w_j\|_2^2\leq9\varepsilon^2. $$

The all-ones vector belongs to $K$ and has norm $\sqrt6$. Consequently,

$$ \mathrm{dist}(\mathbf1,W)\leq\|P_K-P_W\|_F\sqrt6\leq3\sqrt6\varepsilon\lt8\varepsilon. $$

## The oriented denominator contradicts this estimate

Take a nonconstant vanilla denominator. Its aggregate first-block coefficient vector has a uniform strict sign. Sign-normalize it to a nonnegative vector $v$ with coordinate sum one. Then $v\perp W$ and $\|v\|_2\leq1$, so

$$ 1=v\cdot\mathbf1\leq\mathrm{dist}(\mathbf1,W)\lt8\varepsilon. $$

Raising to the fourth power would give

$$ 1\lt4096\varepsilon^4=4096\cdot400000\cdot10^{-10}=0.16384, $$

which is impossible. This proves the stated tensor gap. $\blacksquare$

Scaling the source by any nonzero scalar scales the gap by its absolute value, because the class of vanilla tensors is closed under scaling its numerator coefficients. Turning this tensor gap into an explicit replication threshold additionally requires a quantitative bound for the dense-grid sign-to-polynomial step. That bound is not supplied here.
