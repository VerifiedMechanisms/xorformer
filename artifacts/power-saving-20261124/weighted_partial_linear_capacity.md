# Weighted sign capacity with a linear parameter block

## Status

This note combines the partially linear KKT count with the weighted-degree root count. The degree penalty is paid only by nonlinear variables, and their weight product divides that penalty. The application covers sums of arbitrary curvilinear osculating clusters, with a bound controlled by the entropy of the cluster sizes.

These are written mathematical results. No Lean formalization or reduction of unrestricted affine-ratio scores to the clustered class is asserted.

## The weighted partially linear count

Let $f_1,\ldots,f_m$ be real polynomials in variables $a\in\mathbb R^L$ and $b\in\mathbb R^q$. Suppose they are jointly affine in $a$. Give the nonlinear variables positive integer weights $w_i\leq D$, and suppose every coefficient of each polynomial as an affine function of $a$ has weighted degree at most the integer $D\geq1$ in $b$. Set $p=L+q\geq1$.

### Theorem 1. Explicit bound

The number $T$ of strict sign vectors satisfies

$$ T\leq\frac{(2D)^q}{\prod_{i=1}^q w_i}\binom{2p}{q}\sum_{j=0}^p2^j\binom mj. $$

If $p\leq m$ and $q\gt0$, then

$$ T\leq\left(\frac{2em}{p}\right)^p\left(\frac{4eDp}{q}\right)^q\frac1{\prod_{i=1}^q w_i}. $$

When $q=0$, empty products are one and the second factor is omitted.

**Proof.** Choose a witness for every realized strict sign vector. There are finitely many witnesses, so a sufficiently small positive threshold box preserves all their sign vectors. Sard's theorem permits one threshold vector for which all active equality varieties with at most $p$ equations are smooth of their expected codimension, and no $p+1$ threshold equations hold simultaneously. This is the same finite regular-value argument as in `pencil_cluster_sign_capacity.md`.

For each nonlinear coordinate define $k_i=\lceil D/(2w_i)\rceil$, and use the coercive polynomial

$$ Q_0(a,b)=\sum_{r=1}^L a_r^2+\sum_{i=1}^q b_i^{2k_i}. $$

Its perturbation $Q_u=Q_0-u\cdot(a,b)$ is coercive for every $u\in\mathbb R^p$. On each smooth active equality variety $V$ with $j$ equations, consider the map

$$ \Phi_V(z,\lambda)=\nabla Q_0(z)-\sum_{r=1}^j\lambda_r\nabla f_{i_r}(z),\qquad (z,\lambda)\in V\times\mathbb R^j. $$

Its source and target have dimension $p$. A common regular value $u$ exists for the finite family of these maps. Every closed threshold sign region has a minimizer of $Q_u$. Active-gradient independence supplies its unique multipliers. Regularity of $u$ means that the square KKT Jacobian at the selected root is nonsingular: the constraint rows put a kernel vector in the tangent space of $V$, and the remaining rows identify it with a kernel vector of the displayed map. Thus every chosen minimizer is an isolated nonsingular complex KKT root. Distinct strict sign vectors give distinct selected parameter points.

Group the KKT variables as $(a,\lambda)$, of dimension $L+j$, and $b$, of dimension $q$. The $j$ constraint equations and $L$ stationarity equations in $a$ have degree at most one in the first block and weighted degree at most $D$ in the second.

The stationarity equation for $b_i$ has degree at most two in the first block. Its weighted degree in the second is at most $2D-w_i$. Indeed, the multiplier term has weighted degree at most $D-w_i$. Also $k_iw_i\leq D$: if $w_i\geq D/2$, then $k_i=1$; otherwise $\lceil D/(2w_i)\rceil\leq D/(2w_i)+1\leq D/w_i$. Therefore the objective derivative has weighted degree $(2k_i-1)w_i\leq2D-w_i$.

Translate the nonlinear coordinates generically so that every selected root has all nonlinear coordinates nonzero. Translation preserves the weighted-degree bounds. Substitute $b_i=y_i^{w_i}$. Each selected root lifts to exactly $\prod_iw_i$ distinct nonsingular complex roots, because all power-map derivatives there are nonzero. The transformed system has ordinary two-block degrees bounded by the preceding weighted degrees. The multihomogeneous isolated-root Bezout bound therefore applies, even if other positive-dimensional components occur.

For a fixed active set of size $j$, the number of selected roots is at most the coefficient of $X^{L+j}Y^q$ in

$$ \frac1{\prod_iw_i}(X+DY)^{L+j}\prod_{i=1}^q\big(2X+(2D-w_i)Y\big). $$

Coefficientwise comparison with $2^q(X+DY)^{p+j}/\prod_iw_i$ bounds this by

$$ \frac{(2D)^q}{\prod_iw_i}\binom{p+j}{q}\leq\frac{(2D)^q}{\prod_iw_i}\binom{2p}{q}. $$

There are $\binom mj2^j$ choices of active indices and threshold signs. Summing proves the first bound. The inequalities $\sum_{j=0}^p2^j\binom mj\leq(2em/p)^p$ and $\binom{2p}{q}\leq(2ep/q)^q$ prove the second. $\blacksquare$

The weighted root-lifting step is the same elementary translation and power-map argument used in `weighted_degree_sign_capacity.md`. The two-block isolated-root Bezout statement is [Theorem 1.69 in Spaenlehauer's thesis](https://members.loria.fr/PJSpaenlehauer/data/these_spaenlehauer.pdf), also checked in the preceding partially linear audit.

## Sums of curvilinear osculating clusters

Choose positive integers $m_1,\ldots,m_G$ with total $M$. In cluster $g$, choose affine forms $B_{g,0},\ldots,B_{g,m_g-1}$, with $B_{g,0}$ positive on the Boolean cube, and define

$$ f_{g,r}(x)=[s^r]\frac1{\sum_{j=0}^{m_g-1}B_{g,j}(x)s^j},\qquad 0\leq r\lt m_g. $$

Allow arbitrary affine forms $L_{g,r}$, and consider the score

$$ S(x)=\sum_{g=1}^G\sum_{r=0}^{m_g-1}L_{g,r}(x)f_{g,r}(x). $$

An arbitrary bias is absorbed in any term with $r=0$. The denominator curves, all numerator coefficients, and the cluster sizes may depend on the target.

### Theorem 2. Cluster-entropy bound

Let $N=2^n$, $p=2(n+1)M\leq N$, and $q=(n+1)M=p/2$. For a fixed size list, the number of strict Boolean label tables is at most

$$ T\leq\left(\frac{2eN}{p}\right)^p\frac{(16eM)^q}{\prod_{g=1}^G(m_g!)^{n+1}}. $$

Writing $\rho_g=m_g/M$ and using natural logarithms, this implies

$$ \log T\leq p\log\left(\frac{2eN}{p}\right)+q\left(\log(16e^2)+\sum_{g=1}^G\rho_g\log\frac1{\rho_g}\right). $$

In particular, the last sum is at most $\log G$.

**Proof.** Set $Q_{g,r}=B_{g,0}^{r+1}f_{g,r}$. Give every coefficient of $B_{g,j}$ weight $j+1$. The recurrence

$$ Q_{g,0}=1,\qquad Q_{g,r}=-\sum_{j=1}^r B_{g,j}B_{g,0}^{j-1}Q_{g,r-j} $$

shows that $Q_{g,r}$ has weighted degree $2r$. Clear the positive product $\prod_gB_{g,0}^{m_g}$. The term associated with $(g,r)$ becomes

$$ L_{g,r}Q_{g,r}B_{g,0}^{m_g-r-1}\prod_{h\neq g}B_{h,0}^{m_h}. $$

It is linear in the $q$ numerator coefficients and has nonlinear weighted degree $M+r-1\leq2M$. There are $q$ nonlinear coefficients. Their weight product is $\prod_g(m_g!)^{n+1}$. Theorem 1 with $D=2M$ and $p/q=2$ yields the first bound.

Finally, $m_g!\geq(m_g/e)^{m_g}$ and $\sum_gm_g=M$ give

$$ M\log M-\sum_gm_g\log m_g=M\sum_g\rho_g\log\frac1{\rho_g}. $$

Substitution proves the entropy form. $\blacksquare$

If ordered positive size lists are allowed to vary, there are at most $2^{M-1}$ lists in total. Multiplying by $2^M$ therefore covers every size list, at an additive cost at most $M\log2$ in the logarithmic count.

For any fixed $0\lt\beta\lt1$, this gives a restricted fixed-power lower bound when the number of clusters is at most $\exp(n^\beta)$. More precisely, for all sufficiently large $n$, widths $M\leq N/[100n^{1+\beta}]$ give fewer than $2^N$ labels. The leading entropy contribution divided by $N$ is at most $1/100+o(1)$ in natural logarithms; the arrangement term and size-list term are $o(N)$. Thus the restricted worst-case osculating length is $\Omega(N/n^{1+\beta})$.

For a bounded number of clusters, the exact bound gives the stronger restricted endpoint $\Omega(N/n)$ by choosing a sufficiently small constant in $M=cN/n$.

## Precise remaining gap

Every original score is trivially included by taking one length-one cluster per head. Then $G=M=H$, the entropy can be $\log H$, and the count retains the original order $nH\log H$. The new result is useful only when many heads can be replaced jointly by longer osculating clusters with a controlled total length and a small cluster entropy.

No such replacement has been proved for arbitrary target-dependent finite-scale denominator configurations. Neither positivity of denominators, arbitrary jet weights, nor the existence of a curve through a finite set of denominator coefficient vectors supplies it. The theorem therefore does not prove the requested unrestricted lower bound.
