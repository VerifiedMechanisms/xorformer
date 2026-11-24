# Symmetry and Row Balancing of Head Spaces

## Statement and scope

Put $X=\lbrace0,1\rbrace^n$ and $N=2^n$. Fix $H\geq1$. For strictly positive affine denominators $D_1,\ldots,D_H$, let

$$ U_D=\sum_{h=1}^H D_h^{-1}L,\qquad L=\mathrm{span}\lbrace1,x_1,\ldots,x_n\rbrace\subseteq\mathbb R^X. $$

Let $r$ be the maximum dimension of these spaces. Thus $1\leq r\leq\min(N,1+nH)$. There is an open dense set of admissible denominator lists with the following property: there are positive numbers $s_x$ such that the orthogonal projection $P$ onto $\mathrm{diag}(s)U_D$ has

$$ P_{xx}=\frac rN\qquad\text{for every }x\in X. $$

Every strict sign representation with at most $H$ heads can be perturbed, without changing its labels or head count, to use such a denominator list. No restriction on signs of residues, denominator orientations, or cancellation is imposed.

This is a normalization of the score subspace for analysis. Multiplication by $s_x$ is not asserted to be an admissible head operation. It preserves all coordinate signs, but a uniform bound on the sign patterns of the resulting family of subspaces remains unproved.

## Proof of the normalization

### Theorem 1. Generic ranks inherit cube symmetry

Normalize each denominator by $D_h(0)=1$ and write $D_h=1+b_h\cdot x$. For this generic-rank calculation only, enlarge the manuscript's denominator domain to all affine forms positive on the cube:

$$ \Omega=\lbrace b:1+b_h\cdot x\gt0\text{ for all }h,x\rbrace $$

This is a nonempty open convex set. Unlike the manuscript's admissible domain, it allows mixed slope signs. The enlargement is used only to establish the symmetry of the generic rank function. The space $U_D$ is the column space of the matrix with columns $1$ and $x_i/D_h$. Indeed, $1/D_h=1-\sum_i b_{h,i}x_i/D_h$, and $1=D_h/D_h$ belongs to every summand.

For each subset $T\subseteq X$, let $r(T)$ be the maximum rank of this matrix restricted to $T$, over $\Omega$. A minor attaining $r(T)$ at one point is a nonzero rational function with denominators nonzero throughout $\Omega$. Its numerator is a nonzero polynomial. Its nonvanishing locus is open dense in $\Omega$. Intersect these loci for the finitely many subsets $T$ to obtain an open dense set $\Omega_\ast$ on which all row ranks attain their maxima simultaneously.

Every cube translation $g_v(x)=x\mathbin{\oplus}v$ maps affine tables to affine tables. It permutes positive affine denominator lists, after the positive normalization $D_h\circ g_v\mapsto(D_h\circ g_v)/D_h(v)$. The corresponding head spaces are related by the same row permutation. Consequently

$$ r(g_vT)=r(T). $$

For any $D\in\Omega_\ast$, its row matroid therefore has a transitive group of automorphisms. This conclusion concerns the generic rank function; the numerical matrix itself need not be invariant under cube translations. $\blacksquare$

### Theorem 2. A transitive row matroid admits exact balancing

Let $A$ be a real $N\times r$ matrix of full column rank. Suppose its row matroid is invariant under a transitive permutation group. Let $\mathcal B$ be its nonempty collection of row bases, and put $c=(r/N)\mathbf1$.

The average of the vectors $\mathbf1_B$ over all $B\in\mathcal B$ is invariant under that group and hence constant in every coordinate. Its coordinate sum is $r$, so this average is exactly $c$. In particular, $c$ is a convex combination with a strictly positive coefficient on every basis vector.

For each basis set define $q_B=\det(A_B)^2\gt0$ and $v_B=\mathbf1_B-c$. Let $E=\mathrm{span}\lbrace v_B:B\in\mathcal B\rbrace$. Consider the function on $E$

$$ F(t)=\log\sum_{B\in\mathcal B}q_B e^{\langle v_B,t\rangle}. $$

If $E=\lbrace0\rbrace$, take $t=0$ below. Otherwise, for every unit $u\in E$ there is a basis $B$ with $\langle v_B,u\rangle\gt0$. To prove this, suppose all these inner products are nonpositive. Their average is zero, so every one is zero. Since the $v_B$ span $E$, this forces $u=0$, a contradiction.

By compactness of the unit sphere of $E$, the positive continuous function $u\mapsto\max_B\langle v_B,u\rangle$ has a positive minimum $\delta$. If $q_{\min}=\min_Bq_B$, then

$$ F(t)\geq\log q_{\min}+\delta\lVert t\rVert_2. $$

Thus $F$ attains a minimum $t_\ast$ on $E$. Its gradient is a convex combination of the $v_B$, hence belongs to $E$. Stationarity on $E$ gives a zero gradient in the entire coordinate space. Equivalently, with

$$ \pi_B=\frac{q_Be^{\langle\mathbf1_B,t_\ast\rangle}}{\sum_{C\in\mathcal B}q_Ce^{\langle\mathbf1_C,t_\ast\rangle}},\qquad \sum_{B\ni x}\pi_B=\frac rN. $$

Set $s_x=e^{t_{\ast,x}/2}$ and $Z=A^\top\mathrm{diag}(s^2)A$. Cauchy-Binet gives

$$ \det Z=\sum_{B\in\mathcal B}q_B\prod_{x\in B}s_x^2. $$

Differentiating its logarithm with respect to $t_x$ gives both $\sum_{B\ni x}\pi_B$ and $s_x^2a_x^\top Z^{-1}a_x$, where $a_x^\top$ is row $x$ of $A$. The orthogonal projection onto $\mathrm{diag}(s)\mathrm{im}(A)$ is

$$ P=\mathrm{diag}(s)A Z^{-1}A^\top\mathrm{diag}(s),\qquad P_{xx}=s_x^2a_x^\top Z^{-1}a_x=\frac rN. $$

This proves exact balancing, including matroids with several connected components. The use of a strictly positive combination of all basis vectors ensures attainment; membership in the closed basis polytope alone would not ensure it. $\blacksquare$

### Theorem 3. Strict representations can be perturbed

Take any strictly classifying head sum and hold its affine numerators fixed. Its finitely many positive denominators and signed score values have positive minima. By continuity, all denominator and classification inequalities persist on an open neighborhood of its denominator parameters. First replace every constant denominator by itself plus a sufficiently small positive multiple of $\sum_i x_i$, preserving all strict labels. Each denominator then has either all positive or all negative slopes, exactly as required by the manuscript. Restrict the perturbation neighborhood to preserve each of these strict slope signs. This restricted neighborhood is still open in the enlarged space $\Omega$, so it meets $\Omega_\ast$ by Theorem 1. Perturb inside this intersection and apply Theorem 2 to a column basis of its head space. Every perturbed denominator remains admissible.

Unused heads can have zero numerators. A separate readout constant is already included in $U_D$. This argument is compatible with the manuscript's strictification and positive affine-ratio normal form. $\blacksquare$

## Consequences and exact limitations

For $v\in\mathrm{diag}(s)U_D$, Cauchy-Schwarz applied to $v_x=\langle Pe_x,v\rangle$ gives

$$ |v_x|^2\leq\frac rN\lVert v\rVert_2^2,\qquad \lVert v\rVert_1\geq\sqrt{\frac Nr}\lVert v\rVert_2. $$

More generally, a $k$-dimensional subspace of $\mathrm{diag}(s)U_D$ supported on $T$ requires $|T|\geq kN/r$. Indeed its projection $Q$ satisfies $0\preceq Q\preceq P$, has diagonal zero outside $T$, and has trace $k$. Summing $Q_{xx}\leq P_{xx}=r/N$ over $T$ gives the claim.

For one head, multiplication by its denominator maps $U_D$ exactly onto the fixed affine space $L$. In the Walsh basis $1,(-1)^{x_1},\ldots,(-1)^{x_n}$, the projection onto $L$ has constant diagonal $(n+1)/N$. Thus the general balancing theorem agrees with a direct exact normalization in this case.

Generic perturbation cannot be omitted. For $n\geq5$, choose $n$ distinct positive integers $a_h$, put $t=\sum_i x_i$, and set

$$ R(t)=\frac{\prod_{j=1}^n(t-j)}{\prod_{h=1}^n(t+a_h)}. $$

Polynomial division and partial fractions express $R$ as a constant plus $n$ terms with constant numerators and admissible denominators $t+a_h$. Its table is a nonzero multiple of the coordinate vector at the origin. Therefore $U_D$ contains that coordinate vector, as does every positive diagonal rescaling of $U_D$. Every such projection has $P_{00}=1$. On the other hand, $\dim U_D\leq1+n^2\lt2^n$, so uniform leverage is impossible. This example gives no failure of the generic perturbation statement.

Finally, equal leverage by itself gives no uniform label restriction. For every $y\in\lbrace-1,1\rbrace^X$, the one-dimensional space $\mathrm{span}\lbrace y\rbrace$ has projection $yy^\top/N$ and hence diagonal $1/N$. The collection of all these balanced lines realizes every labeling. These lines are not asserted to be one-head spaces. They show precisely why balancing must be combined with a bound on the particular denominator-dependent family.

## Literature and remaining gap

The determinant objective and basis-polytope method are the standard mechanism behind Barthe and Forster normalization. [Hardt and Moitra, Section 4](https://proceedings.mlr.press/v30/Hardt13.pdf), connect this mechanism to robust subspace recovery. [Jambulapati, Li, and Tian, Section 2.2](https://arxiv.org/html/2504.05687v1), give the leverage-score formulation. The proof above establishes attainment directly from the positive average of all bases, so it does not need a boundary attainment claim for general basis-polytope points.

The application here is the simultaneous generic-rank argument using cube translations. It supplies a global normalization covering every strict Boolean representation after perturbation. It does not bound the number of oriented matroids, the metric entropy of the normalized family, or the number of orthants that family meets. A bound on this family strong enough to refute the requested upper bound remains a theorem-strength gap. No asymptotic head-count improvement follows at this checkpoint.

## Verification scope

The three general theorems above have complete written proofs. They are not end-to-end Lean declarations. `SymmetricRowBalancing.lean` checks eight finite ingredients: translation invariance of sums, the constant-average identity, sign preservation under positive scaling, a squared-mass inequality, the supported-trace bound, and the diagonal, idempotence, and fixed-vector identities for balanced sign lines.

An independent exact rational verifier checks three small head spaces, their complete basis families and translation symmetries, and explicit balanced projections. It also checks the partial-fraction point-mass construction in five dimensions of input size, from five through nine bits, and all 256 sign-line projections on eight coordinates. These checks supplement the general written proofs. They are not numerical evidence for an unrestricted head lower bound.
