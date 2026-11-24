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

Every six-row determinant of $V$ has absolute value at least $v$, by its Vandermonde formula. All $\mu_h$ and $\delta$ are positive. Put

$$ d=4v^2(\mu_0\mu_1\mu_2)^2,\qquad \lambda=\frac{4\delta^6v^2}{12^{11}10^{10}},\qquad K=1+\frac{240\cdot19^5}{d}. $$

A valid exclusion radius is

$$ \rho=\min\left(1,\frac{d}{10^4\cdot19^5},\frac{1}{10^6K^2},\frac{\lambda}{10^{14}K^3}\right). $$

Exact rational arithmetic gives $\rho\gt2^{-2000}$. None of these constants depends on a competing representation.

## A raw coefficient gap from Hessian rank

Orient one nonzero denominator direction to have positive coefficients and normalize their sum to one; denote it by $D$. If all denominator directions are zero, then $R=0$ and any positive normalized direction may be used for $D$. Let $\mathbf{1}$ be the all-ones vector and $\pi z=z-D(z)\mathbf{1}$. Each restricted form $B_h\pi$ has a coefficient of absolute value at least $\delta$. Indeed, if $\sum_i b_{h,i}$ is nonnegative, choose a negative coefficient of $B_h$; subtracting a nonnegative multiple of a coefficient of $D$ can only increase its absolute value. If that sum is negative, choose a positive coefficient instead.

Use the finite grid $\lbrace-1,-1/2,0,1/2,1\rbrace^{14}$. For a linear form with one coefficient of magnitude at least $\delta$, fixing the other thirteen coordinates makes successive values differ by at least $\delta/2$. At most one of those five values can lie in the interval $(-\delta/12,\delta/12)$, whose length is $\delta/6$. Thus each of the three restricted forms has at most $5^{13}$ bad grid points. Their union has at most $3\cdot5^{13}\lt5^{14}$ points. Choose a remaining point $z$; all three $|B_h(\pi z)|$ are at least $\delta/12$. Set $w=\pi z$; its coordinates have magnitude at most two. This is a finite counting argument, with no probabilistic or limiting existence assumption.

In the six latent coordinates $(S_0,S_1,S_2,B_0,B_1,B_2)$, the Hessian of $P_3$ has block form

$$ H=\begin{pmatrix}0&A\cr A^{\top}&L\end{pmatrix},\qquad \det H=-4(B_0B_1B_2)^2. $$

The off-diagonal entries of $A$ are the remaining $B$ coordinates, and its diagonal is zero. At $w$, $H$ is invertible. Every entry has magnitude less than two, so its operator norm is at most twelve. Its least singular value is at least $4\delta^6/12^{11}$, by the determinant formula and the upper bound on its other five singular values.

Every entry of $V$ has magnitude less than one, and its operator norm is less than ten. Its least singular value is at least $v/10^5$, since its first six rows have determinant $v$. Thus the six nonzero singular values of the ambient Hessian $VH V^{\top}$ are at least $\lambda$. To see this explicitly, take a thin QR factorization $V=QR$; the nonzero part is $RHR^{\top}$, and its inverse has operator norm at most $\|R^{-1}\|^2\|H^{-1}\|$.

The ambient Hessian of $R$ is a linear pullback of the same six-coordinate Hessian template, with latent coordinates $(N_0,N_1,N_2,D_0,D_1,D_2)$. At $w$, the chosen denominator direction vanishes. The determinant formula therefore makes this latent Hessian singular, so the ambient Hessian of $R$ has rank at most five. If all denominator directions are zero, its rank is zero. It cannot differ from the target Hessian by operator norm less than $\lambda$: intersect the six-dimensional range of the target Hessian with the kernel of the rank-at-most-five competitor. On a unit vector in this intersection, the Hessian difference has norm at least $\lambda$.

If every raw cubic coefficient differs by at most $\varepsilon$, then at a point of coordinate norm at most two every Hessian entry differs by at most $168\varepsilon$, and the operator norm differs by at most $2352\varepsilon$. Therefore raw coefficient error below $\lambda/2352$ is impossible. Zero denominator directions were included in the argument above. Since the gap is uniform, it also applies to the closure.

## Quantitative recovery from squarefree coefficients

Every Hessian of $R$ has rank at most six, since $R$ depends on at most six linear forms. Fix distinct coordinates $i,k$. In the Hessian at $e_k$, choose disjoint six-element row and column sets avoiding $i,k$. The target cross block has determinant of absolute value at least $d$: it factors into two six-row determinants of $V$ and the latent Hessian determinant at $e_k$.

Suppose all squarefree coefficient errors are at most $\varepsilon\leq\rho$. Ordinary monomial coefficients are used throughout, without factorial normalization. Each coefficient of $P_3$ has magnitude at most eighteen, by expanding its three products of three forms whose coefficients have magnitude less than one. All entries of the target cross block are squarefree coefficients and have the same bound. A six-by-six determinant changes by at most $4320\cdot19^5\varepsilon$ when all entries change by at most $\varepsilon\leq1$. Thus every chosen cross block remains invertible, and every entry of both its inverse and the target inverse is at most $K$ in absolute value. The inverse difference has each entry at most $36K^2\varepsilon$.

For either Hessian $M$, rank at most six gives the Schur identity

$$ M_{ii}=M_{i,B}(M_{A,B})^{-1}M_{A,i}. $$

All entries on the right are squarefree coefficients. Expanding the difference of the three factors shows that each recovered coefficient of $x_i^2x_k$ has error at most

$$ L\varepsilon,\qquad L=2000K+500000K^2. $$

The definition of $\rho$ ensures $L\varepsilon\lt1$. To recover $x_k^3$, apply the same Schur identity with row index $k$ and any disjoint cross block avoiding $k$. Its row and column now use the just-recovered repeated-index coefficients. Their target entries have magnitude at most thirty-six and their errors are at most $2L\varepsilon$. Expansion gives an error at most $(6000LK+2000000K^2)\varepsilon$ for the recovered Hessian diagonal, hence also for the cubic coefficient.

Every raw coefficient error is therefore less than $10^{10}K^3\varepsilon$. For $\varepsilon\leq\rho$, this is less than $\lambda/2352$, contradicting the raw coefficient gap. This proves the stated squarefree exclusion. $\blacksquare$

## Lean coverage

The exact rank and recovery statements used here are kernel checked in the following files:

- [`LowRankCrossRecovery.lean`](../../../formalization/HeadComplexity/Polynomial/LowRankCrossRecovery.lean): `entry_of_rank_le` proves the Schur identity for every entry, and `diagonal_of_rank_six` specializes it to the diagonal recovery above.

- [`SymmetricCubicRecovery.lean`](../../../formalization/HeadComplexity/Polynomial/SymmetricCubicRecovery.lean): `eq_of_squarefree` proves uniqueness of the full symmetric cubic tensor from its squarefree entries under the rank-six and invertible-cross-block hypotheses.

- [`ThreeHeadPoleHessian.lean`](../../../formalization/HeadComplexity/Polynomial/ThreeHeadPoleHessian.lean): `hessian_rank_le_five_at_pole` proves the ambient rank bound at every denominator pole. `mixed_independent_cubic_ne_oriented` proves the complete exact raw-polynomial obstruction whenever the six forms have an invertible six-row minor and each target denominator form has both signs. It includes arbitrary numerator coefficients and zero competitor denominator directions. [`ExplicitCubicRawObstruction.lean`](../../../formalization/HeadComplexity/Polynomial/ExplicitCubicRawObstruction.lean) instantiates this theorem to the exact fourteen-variable rational target, including a free readout term, and checks its six-row minor by an explicit rational inverse.

- [`HyperplaneHessianRank.lean`](../../../formalization/HeadComplexity/Polynomial/HyperplaneHessianRank.lean): `rank_compression` proves that a rank-one projection loses at most two ranks; `eval_product_hessian` identifies the actual polynomial Hessian of a product of three linear forms; `tripleHessian_rank_le` bounds its rank by three. Consequently `compression_ne_tripleHessian` excludes equality after compressing any matrix of rank at least six.

- [`GenericCubicHessian.lean`](../../../formalization/HeadComplexity/Polynomial/GenericCubicHessian.lean): `eval_second_pderiv` identifies the six-variable polynomial Hessian, `hessian_det` proves its determinant formula, and `hessian_rank` proves rank six when the three denominator coordinates are nonzero. [`GenericCubicHessianPullback.lean`](../../../formalization/HeadComplexity/Polynomial/GenericCubicHessianPullback.lean) proves the actual ambient Hessian pullback identity and the rank-at-most-six bound, including an arbitrary readout term.

- [`FiniteGridAvoidance.lean`](../../../formalization/HeadComplexity/Polynomial/FiniteGridAvoidance.lean): `exists_fourteen_cube_point` kernel checks the five-point grid counting argument and its simultaneous lower bounds for three linear forms.

These declarations use no `sorry` or new axioms. The numerical norm estimates and quantitative stability bounds in this note remain mathematical proofs with exact arithmetic certificates; they are not presented as a complete Lean proof of the exclusion radius.
