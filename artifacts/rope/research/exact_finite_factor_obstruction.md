# The Source Cubic Has No Exact Oriented Finite-Factor Representation

This note strengthens the four-factor obstruction to every finite number of factors. It is a rigorous mathematical statement about polynomial identities and sign agreement on an open continuous cube. It does not strengthen the proved finite Boolean lower bound beyond four vanilla heads. The limit and replica-averaging gaps stated at the end remain essential.

## A residue obstruction

Let $R$ be a polynomial ring over the reals, graded by total degree. Let $P$ be a nonzero homogeneous polynomial of degree $d\geq 2$. Suppose $L_1,\ldots,L_H$ are nonzero, pairwise nonproportional linear forms. Assume that, for every $i$, the image of $P$ in the quotient polynomial ring $R/(L_i)$ is nonzero and has an irreducible factor of degree at least two.

Then there are no nonzero polynomial $G$ and linear forms $A_i$ satisfying

$$ P G=\sum_{i=1}^{H} A_i\prod_{j\neq i}L_j. $$

Here zero linear numerators are allowed.

**Proof.** A nonzero right side is homogeneous of degree $H$, so the identity forces $G$ to be homogeneous of degree $H-d$. If $H\lt d$, the identity is already impossible.

Reduce the identity modulo $L_i$. Because the denominator forms are pairwise nonproportional, every image of $L_j$ with $j\neq i$ is a nonzero linear form. Thus

$$ \overline P\overline G=\overline {A_i}\prod_{j\neq i}\overline {L_j}. $$

The quotient ring is a polynomial ring and hence a unique factorization domain. If $\overline {A_i}\neq 0$, every irreducible factor of the right side has degree one. The left side has an irreducible factor of degree at least two, which is impossible. Therefore $\overline {A_i}=0$, and the integral-domain property gives $\overline G=0$. Consequently $L_i$ divides $G$.

All $H$ pairwise nonproportional linear forms divide $G$, so their product divides $G$. This forces $\deg G\geq H$, contradicting $\deg G=H-d$. $\blacksquare$

The same argument works if a free score constant is included, since it can be absorbed into any one numerator. Repeated proportional denominator factors can first be combined. These operations leave a collection of distinct denominator forms and linear numerators.

## Hyperplane sections of the source cubic

Use independent linear coordinates $D_1,D_2,D_3,N_1,N_2,N_3$, together with any number of unused coordinates, and set

$$ P=N_1D_2D_3+N_2D_1D_3+N_3D_1D_2. $$

The previously proved classification in [the four-factor note](exact_four_factor_obstruction.md) states that the two-dimensional spaces $U$ satisfying $P\in(U)$ are exactly

$$ \mathrm{span}(D_i,D_j)\quad(i\neq j),\qquad U_i=\mathrm{span}(D_i,N_i)\quad(i=1,2,3). $$

In the physical source coordinates, the denominator slope rows are independent and have coordinate sum zero. A nonzero homogeneous affine form with strictly uniform slopes, or with zero slopes and a nonzero constant, cannot belong to any $\mathrm{span}(D_i,D_j)$. Call such forms oriented.

Let $L$ be an oriented form. Since $P$ is irreducible of degree three, its image $\overline P$ modulo $L$ is nonzero. If $\overline P$ is reducible, its homogeneous degree three implies that it has a linear factor $\overline A$. Lifting this factor gives $P\in(L,A)$, with $L,A$ independent. The classification therefore forces

$$ \mathrm{span}(L,A)=U_i $$

for one index $i$. In particular $L=aD_i+bN_i$. Its orientation excludes $b=0$.

For the other two indices $j,k$, eliminate $N_i$ using $L=0$. The source section becomes

$$ \overline P=D_i Q,\qquad Q=N_jD_k+N_kD_j-\frac{a}{b}D_jD_k. $$

The quadratic form $Q$ has rank four in the independent coordinates $N_j,N_k,D_j,D_k$. Indeed its symmetric matrix has block form

$$ \begin{pmatrix}0&B\cr B^\top&C\end{pmatrix},\qquad B=\frac12\begin{pmatrix}0&1\cr1&0\end{pmatrix}, $$

where $B$ is invertible, so the whole matrix is invertible regardless of $C$. A product of two linear forms has quadratic rank at most two. Thus $Q$ is irreducible over the reals.

It follows that every oriented section $\overline P$ has an irreducible factor of degree at least two: either it is itself irreducible of degree three, or it has the irreducible quadratic factor just displayed. Unused coordinates do not alter this conclusion; the rank argument remains valid, and the zero-space classification already included unused coordinates.

## Exact polynomial and continuous-cube consequences

Applying the residue obstruction gives the following statement for every finite $H$:

$$ P G\neq \sum_{i=1}^{H} A_i\prod_{j\neq i}L_j $$

whenever $G\neq 0$, the $A_i$ are arbitrary linear forms, and the $L_i$ are pairwise nonproportional oriented denominator forms.

This covers physical affine forms by homogenization. The homogenizing coordinate is independent of the six displayed source coordinates. In particular nonzero constant denominators are covered. Proportional factors can be combined before applying the result.

Consequently no finite sum of affine fractions with oriented positive affine denominators agrees with the source classification on the entire open physical cube. Such an agreement would force its cleared polynomial to vanish on an open smooth patch of the source zero set. The established local divisibility theorem and irreducibility then make that cleared polynomial a nonzero multiple $P G$, contrary to the residue obstruction. The cleared polynomial is nonzero because the source has both signs near the origin. A constant score also cannot agree with both signs.

The source is therefore a useful example where every finite-grid classifier has a finite vanilla realization, but no single finite collection of these oriented affine fractions represents the same boundary on the continuous cube.

## What this does not prove

For each fixed finite Boolean grid, a vanilla score may have the same strict-positive classification without its cleared polynomial being divisible by $P$. A sequence of grid representations can also have colliding denominator forms and divergent numerator coefficients. The normalized limit polynomial need not retain an exact representation with distinct linear denominator factors, so the residue proof cannot be applied to that limit without an additional closure theorem.

Moreover, replica averaging preserves the selected top mixed coefficients used in the proved three-head separation, rather than preserving a full affine-fraction factorization. Thus this exact identity obstruction does not establish a finite-family lower bound of five, six, or an unbounded number of heads. The fully proved finite-family interval remains four through six vanilla heads for all sufficiently large replication counts.
