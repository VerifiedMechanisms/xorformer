# A uniform exclusion radius for vanilla three-head cubic tensors

## Statement

Use the fourteen-coordinate rational forms $S_h,B_h$ from [the generic cubic certificate](../generic_cubic_completion/README.md), and put

$$ P_3=S_0B_1B_2+S_1B_0B_2+S_2B_0B_1. $$

A vanilla three-head cleared cubic has the form

$$ R=N_0D_1D_2+N_1D_0D_2+N_2D_0D_1, $$

where each homogeneous denominator direction has strictly uniform coordinate signs or is zero. Its numerator directions are arbitrary. The maximum difference between the squarefree cubic coefficients of $R$ and $P_3$ is greater than $2^{-2000}$. The same exclusion holds for the closure of this class. This permits arbitrary untied vanilla parameters and unbounded numerator coefficients.

This note proves a coefficient bound used in the finite Boolean replication argument. The proof is mathematical; `verify_gap.py` checks all arithmetic inequalities for its explicit rational constants. The underlying mass and matrix-minor certificates are checked by `../generic_cubic_completion/verify.py`.

## Explicit constants

Write $V$ for the fourteen-by-six matrix with rows $(s_{0,i},s_{1,i},s_{2,i},b_{0,i},b_{1,i},b_{2,i})$. Define

$$ v=\frac{34560}{10^{39}},\qquad \delta=\min_h\min\left(\max_i b_{h,i},-\min_i b_{h,i}\right),\qquad \mu_h=\min_i|b_{h,i}|. $$

Every six-row determinant of $V$ has absolute value at least $v$, by its Vandermonde formula. All $mu_h$ and $\delta$ are positive. Put

$$ d=4v^2(\mu_0\mu_1\mu_2)^2,\qquad \lambda=\frac{4\delta^6v^2}{12^{11}10^{10}},\qquad K=1+\frac{240\cdot19^5}{d}. $$

A valid exclusion radius is

$$ \rho=\min\left(1,\frac{d}{10^4\cdot19^5},\frac{1}{10^6K^2},\frac{\lambda}{10^{14}K^3}\right). $$

Exact rational arithmetic gives $\rho\gt2^{-2000}$. None of these constants depends on a competing representation.

## A raw coefficient gap from Hessian rank

Orient one nonzero denominator direction to have positive coefficients and normalize their sum to one; denote it by $D$. Let $\mathbf{1}$ be the all-ones vector and $\pi z=z-D(z)\mathbf{1}$. Each restricted form $B_h\pi$ has a coefficient of absolute value at least $\delta$. Indeed, if $\sum_i b_{h,i}$ is nonnegative, choose a negative coefficient of $B_h$; subtracting a nonnegative multiple of a coefficient of $D$ can only increase its absolute value. If that sum is negative, choose a positive coefficient instead.

For a uniform random point $z$ in the fourteen-dimensional unit cube, a linear form with one coefficient of magnitude at least $\delta$ has probability at most $1/12$ of lying in $(-\delta/12,\delta/12)$. This follows by conditioning on the other thirteen coordinates and measuring an interval. The union bound therefore supplies a point $z$ for which all three $|B_h(\pi z)|$ are at least $\delta/12$. Set $w=\pi z$; its coordinates have magnitude at most two.

In the six latent coordinates $(S_0,S_1,S_2,B_0,B_1,B_2)$, the Hessian of $P_3$ has block form

$$ H=\begin{pmatrix}0&A\cr A^{\top}&L\end{pmatrix},\qquad \det H=-4(B_0B_1B_2)^2. $$

The off-diagonal entries of $A$ are the remaining $B$ coordinates, and its diagonal is zero. At $w$, $A$ is invertible. Completing the square shows that $H$ has three positive and three negative eigenvalues. Every entry has magnitude less than two, so its operator norm is at most twelve. Its least singular value is at least $4\delta^6/12^{11}$, by the determinant formula and the upper bound on its other five singular values.

Every entry of $V$ has magnitude less than one, and its operator norm is less than ten. Its least singular value is at least $v/10^5$, since its first six rows have determinant $v$. Thus the six nonzero eigenvalues of the ambient Hessian $VH V^{\top}$ have absolute value at least $\lambda$. Restriction to the codimension-one space $\ker D$ retains at least two positive and two negative eigenvalues of magnitude at least $\lambda$, by the variational characterization of eigenvalues.

The restriction of $R$ to $\ker D$ is a product of three linear forms, or zero. Its Hessian consequently has rank at most three. It cannot differ from the restricted Hessian of $P_3$ by operator norm less than $\lambda$: intersect a four-dimensional subspace on which the latter has all singular values at least $\lambda$ with the kernel of the rank-three matrix.

If every raw cubic coefficient differs by at most $\varepsilon$, then at a point of coordinate norm at most two every Hessian entry differs by at most $168\varepsilon$, and the operator norm differs by at most $2352\varepsilon$. Therefore raw coefficient error below $\lambda/2352$ is impossible. Zero denominator directions are included by arbitrarily small positive perturbations of those directions, for each fixed numerator list. This also proves the same gap for the closure.

## Quantitative recovery from squarefree coefficients

Every Hessian of $R$ has rank at most six, since $R$ depends on at most six linear forms. Fix distinct coordinates $i,k$. In the Hessian at $e_k$, choose disjoint six-element row and column sets avoiding $i,k$. The target cross block has determinant of absolute value at least $d$: it factors into two six-row determinants of $V$ and the latent Hessian determinant at $e_k$.

Suppose all squarefree coefficient errors are at most $\varepsilon\leq\rho$. Ordinary monomial coefficients are used throughout, without factorial normalization. Each coefficient of $P_3$ has magnitude at most eighteen, by expanding its three products of three forms whose coefficients have magnitude less than one. All entries of the target cross block are squarefree coefficients and have the same bound. A six-by-six determinant changes by at most $4320\cdot19^5\varepsilon$ when all entries change by at most $\varepsilon\leq1$. Thus every chosen cross block remains invertible, and every entry of both its inverse and the target inverse is at most $K$ in absolute value. The inverse difference has each entry at most $36K^2\varepsilon$.

For either Hessian $M$, rank at most six gives the Schur identity

$$ M_{ii}=M_{i,B}(M_{A,B})^{-1}M_{A,i}. $$

All entries on the right are squarefree coefficients. Expanding the difference of the three factors shows that each recovered coefficient of $x_i^2x_k$ has error at most

$$ L\varepsilon,\qquad L=2000K+500000K^2. $$

The definition of $\rho$ ensures $L\varepsilon\lt1$. To recover $x_k^3$, apply the same Schur identity with row index $k$ and any disjoint cross block avoiding $k$. Its row and column now use the just-recovered repeated-index coefficients. Their target entries have magnitude at most thirty-six and their errors are at most $2L\varepsilon$. Expansion gives an error at most $(6000LK+2000000K^2)\varepsilon$ for the recovered Hessian diagonal, hence also for the cubic coefficient.

Every raw coefficient error is therefore less than $10^{10}K^3\varepsilon$. For $\varepsilon\leq\rho$, this is less than $\lambda/2352$, contradicting the raw coefficient gap. This proves the stated squarefree exclusion. $\blacksquare$
