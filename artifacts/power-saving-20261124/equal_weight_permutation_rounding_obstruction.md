# No uniform equal-weight rounding of arbitrary permutation dictionaries

## Status

This is a new exact obstruction to one proposed rounding step in `shared_permutation_dictionary.md`. It is not a lower bound on unrestricted head complexity. For every prescribed integer $K\geq1$, a rational dictionary on only three Boolean inputs and four heads has a universally feasible convex relaxation, but one fixed Boolean target is missed by every sum of at most $K$ permutation branches. The dictionary depends on $K$. Equal weights and the fixed dictionary are essential restrictions.

The proof below is elementary linear algebra and planar convex geometry. `check_equal_weight_rounding_obstruction.py` verifies the displayed rational identities and the parameterized matrices with exact symbolic arithmetic. This is distinct from Lean kernel verification, which has not been performed.

## 1. Dictionary and free space

Order the three-bit cube lexicographically as $000,001,010,011,100,101,110,111$. Define

$$ p(x)=1+x_1+2x_2+4x_3,\qquad c_1(x)=\frac1{p(x)+1},\qquad c_2(x)=\frac1{p(x)+2},\qquad V=\mathrm{span}(1,x_1,x_2,x_3,c_1,c_2). $$

Every denominator is strictly positive on the entire cube and has strictly positive slopes. Numerators used below are arbitrary affine forms, as allowed by the original model.

Let $Q:\mathbb R^8\to\mathbb R^2$ have the following two rows:

$$ Q=\begin{pmatrix}-143&1988&-2895&1050&1193&-3038&1845&0\cr106&1001&399&-1506&-505&-602&0&1107\end{pmatrix}. $$

Exact rational calculation gives $\dim V=6$, $\mathrm{rank}(Q)=2$, and $Q(V)=0$. Consequently $\ker Q=V$.

For $b\in\mathbb R^3$, put $D(b)(x)=(b\cdot x)(c_1(x)-c_2(x))$. Then

$$ QD=\begin{pmatrix}320/3&-206/3&23/3\cr-608/15&34/3&67/15\end{pmatrix}. $$

The determinant of the first two columns is $-7872/5\neq0$. Thus every rational vector in $\mathbb R^2$ is $QD(b)$ for a rational $b$ whose third coordinate is zero.

## 2. One orthant projects to a pointed cone

Fix the target

$$ y=(-1,1,-1,-1,1,-1,1,1),\qquad O_y=\lbrace z\in\mathbb R^8:y_i z_i\gt0\text{ for all }i\rbrace. $$

Write $u=(143,-106)$ and $v=(-1050,1506)$. Their determinant is $104058\gt0$. The eight vectors $y_iQe_i$, in order, are

$$ (143,-106),\ (1988,1001),\ (2895,-399),\ (-1050,1506),\ (1193,-505),\ (3038,602),\ (1845,0),\ (0,1107). $$

They all belong to the closed cone $C=\lbrace au+bv:a,b\geq0\rbrace$, and both boundary generators occur. This follows either directly from their nonnegative determinants with $u$ and $v$, or from the exact script. All have positive coordinate sum, so $C$ is pointed.

It follows that $Q(O_y)$ is exactly the interior of $C$. One inclusion holds because every vector of $O_y$ is a strictly positive combination of the signed coordinate vectors, including both extreme rays. Conversely, take any interior point of $C$. Subtract a sufficiently small positive multiple of the sum of all eight displayed generators. The remainder is still in $C$ and can be written with nonnegative coefficients on $u$ and $v$. Restoring the subtracted sum gives strictly positive coefficients on all eight generators, hence an element of $Q(O_y)$.

## 3. A rational change of coordinates hides every bounded lattice point

Fix an integer $K\geq1$. Let $E_K$ be the open cone between the rays $(K+2,1)$ and $(K+1,1)$. Every $(a,b)\in E_K$ satisfies

$$ b\gt0,\qquad (K+1)b\lt a\lt(K+2)b. $$

There is therefore no integer point in $E_K$ with $|a|,|b|\leq K$. Indeed, a positive integer $b$ is at least one, forcing $a\gt K+1$.

Define the integer matrix

$$ T_K=\begin{pmatrix}1193&-1193K-2243\cr-1612&1612K+3118\end{pmatrix}. $$

Its columns are $u-v$ and $-(K+1)u+(K+2)v$. Then

$$ T_K(K+2,1)^{\top}=u,\qquad T_K(K+1,1)^{\top}=v,\qquad\det T_K=104058. $$

Thus $T_K(E_K)$ is the interior of $C$. By the surjectivity of $QD$, choose rational $b_1,b_2\in\mathbb R^3$ satisfying

$$ QD(b_1)=T_K(1,0)^{\top},\qquad QD(b_2)=T_K(0,1)^{\top}. $$

These vectors can be chosen with third coordinate zero. Their coefficients grow only linearly with $K$; no limiting or infinite coefficient is used.

## 4. Four heads realize the required branch geometry

Use the four numerator slope vectors $b_1,-b_1,b_2,-b_2$ and the pole multiset $(1,1,2,2)$. For every assignment of these poles to the four vectors, let $g_\pi$ be the resulting sum of the four affine-numerator reciprocal heads. The numerator slopes sum to zero. Therefore

$$ g_\pi=D\left(\sum_{h:\lambda_{\pi(h)}=1}b_h\right). $$

Choosing two of $b_1,-b_1,b_2,-b_2$ gives exactly the possible sums $0$ and $\pm b_1\pm b_2$. Consequently

$$ \lbrace Qg_\pi:\pi\rbrace=\lbrace0\rbrace\cup\lbrace T_K(\sigma_1,\sigma_2)^{\top}:\sigma_1,\sigma_2\in\lbrace-1,1\rbrace\rbrace. $$

The convex hull of these projected offsets is the parallelogram $T_K([-1,1]^2)$, which contains zero in its interior. Since $\ker Q=V$, the family

$$ V+\mathrm{conv}\lbrace g_\pi:\pi\rbrace $$

meets every strict coordinate orthant. To prove this explicitly, for any strict table $z$, choose $\eta\gt0$ so small that $Q(\eta z)$ lies in the projected parallelogram. Some convex combination $g$ then satisfies $Q(\eta z-g)=0$, giving $\eta z-g\in V$.

Now consider any $J\leq K$ permutation branches, with repetition permitted, and add an arbitrary table from $V$. Its projection is $T_K(a,b)^{\top}$ for integers $a,b$ with $|a|,|b|\leq J\leq K$. This projected table cannot lie in $Q(O_y)$: that would require $(a,b)\in E_K$, contrary to Section 3. Hence no such sum strictly realizes $y$.

The same conclusion holds for the average of $J$ branches, or a common positive rescaling of their sum, because $Q(O_y)$ is a cone and $V$ is a linear space. $\blacksquare$

## 5. Precise limitation

This theorem rules out a uniform fixed number of equal-weight branches for rounding every universally feasible dictionary relaxation, even with unrestricted real coefficients in its free space. It does not rule out choosing a special universal dictionary, using arbitrary branch-dependent weights, changing denominator directions, or constructing a different original-model representation of the target.

Arbitrary convex combinations already suffice by the proof. Their row-dependent weights are not automatically covered by the one-hot patch compiler: multiplying a shared numerator slope by a row-dependent weight produces a product of a row coordinate and a data coordinate, while each original numerator must be affine. No impossibility theorem for a different weighted compiler is claimed.

The unrestricted exponent improvement remains open in this research run.
