# Limits of Two Further Head-Compression Routes

These are obstructions to particular algebraic simulation constructions. They do not establish a Boolean lower bound of five or six heads. The full Boolean separation proved in Theorem 22 remains three pure heads versus at least four vanilla heads.

## Deleting more terms from the alternating subset construction

Treat $N_1,N_2,N_3,D_1,D_2,D_3$ as independent affine coordinates. This independence is present in the physical source after its invertible coordinate change. Choose the positive uniformly oriented endpoint $F=N_1-tD_1$. Numerator gauge changes replace each $N_i$ by $N_i+c_iD_i$, and the perturbations used in the subset compiler add further combinations of the denominator coordinates.

For a subset $I$, the coefficient of $N_i$ in its subset numerator is one precisely when $i\in I$. The denominator of that term is $F+\varepsilon\sum_{i\in I}D_i$. If this numerator is a constant multiple of its denominator, comparison of the independent numerator coordinates forces $I=\varnothing$ or $I=\lbrace1\rbrace$. Consequently the existing deletion of the empty subset and one singleton cannot be extended to a third subset by denominator gauge adjustments alone.

A centered finite-difference cube does not fix this problem. Its numerator directions have coefficients in $\lbrace-1,1\rbrace^3$. Two such directions are proportional only when they are equal or antipodal. A suitable perturbation can make the two antipodal terms constant, but it again removes only two of the eight terms.

This reasoning allows arbitrary coefficients in the denominator-only gauge terms. It does not rule out changing the finite-difference stencil, changing the target score within its Boolean sign class, or combining rational terms by a different construction.

## Five common-base heads with denominator directions in the original span

After using one positive endpoint, the cleared source cubic has the form

$$ P=F D_2D_3+D_1(N_2D_3+N_3D_2). $$

The six displayed affine coordinates are independent. Consider a common-base construction with $K$ denominators $F+\varepsilon L_a$, where every $L_a$ belongs to the three-dimensional span of $D_1,D_2,D_3$. Allow affine numerators with Laurent coefficients through order $\varepsilon^{-2}$, and suppose the resulting rational score has the polynomial limit $P/F^3$.

For each of the two outside numerator coordinates $N_2,N_3$, let $r^{(j)}_a$ be its coefficient in the $\varepsilon^{-2}$ numerator term. Cancellation of the two divergent orders forces

$$ \sum_a r^{(j)}_a=0,\qquad\sum_a r^{(j)}_aL_a=0. $$

The finite limit, after comparison of terms independent of $F$, then requires

$$ \sum_a r^{(2)}_aL_a^2=D_1D_3,\qquad\sum_a r^{(3)}_aL_a^2=D_1D_2. $$

Subleading affine numerator corrections contribute terms divisible by $F$ and therefore cannot change these two identities.

Let $r$ be the affine-hull dimension of the points $L_a$. The space of coefficient vectors having zero total mass and zero first moment has dimension $K-r-1$. If $K\leq5$ and $r=3$, this dimension is at most one. Its quadratic moment image therefore cannot contain the two independent quadratics on the right.

If $r\leq2$, choose one point $L_0$ and write $V=\mathrm{span}\lbrace L_a-L_0\rbrace$. Zero mass and first moment give

$$ \sum_a s_aL_a^2=\sum_a s_a(L_a-L_0)^2\in\mathrm{Sym}^2(V). $$

Thus both required quadratics would use at most two essential linear coordinates. This is impossible: the linear spans of their first derivatives together contain $D_1,D_2,D_3$, which are independent. Hence this common-base ansatz requires at least six heads.

The conclusion is restricted to the stated polynomial limit and denominator-direction span. It does not exclude perturbations involving the other numerator directions, several distinct limiting denominator bases, more complicated degenerations, or representations chosen solely to preserve signs on a finite Boolean cube. Those alternatives remain relevant to determining whether the separating family has vanilla minimum four, five, or six.
