# Generic radial collisions have low-degree initial tables

## Status and scope

This note proves a new restricted theorem. For a nonempty Zariski-open set of fixed radial directions around a constant denominator, every bounded limit table from the full affine-numerator span has controlled Boolean polynomial degree. Numerator coefficients may vary arbitrarily with the scale; they need not be bounded, analytic, or have bounded jet order. A Hamming-code packing proves that the required open set exists.

The theorem does not apply to arbitrary finite-scale denominator configurations. It does not prove the requested improvement for unrestricted worst-case head complexity. Exceptional direction configurations are substantive: aligned directions can realize high-degree parity using few heads. No reduction of unrestricted representations to the generic radial regime is asserted.

## Definitions

Put $X=\lbrace 0,1\rbrace^n$ and $N=2^n$. Let $\mathcal P_K$ be the vector space of real tables on $X$ whose unique multilinear polynomial has degree at most $K$, and set

$$ D_K=\dim\mathcal P_K=\sum_{j=0}^K\binom nj. $$

Fix affine functions $C_h(x)=c_{h0}+\sum_{i=1}^n c_{hi}x_i$ for $1\leq h\leq H$. For a positive real scale $t$, define the linear table space

$$ V_C(t)=\mathrm{span}_{\mathbb R}\left(\lbrace 1\rbrace\cup\left\lbrace \frac{x_i}{1+tC_h(x)}:1\leq h\leq H,\quad 1\leq i\leq n\right\rbrace\right), $$

whenever the denominators are positive. This space includes every score with these denominators, arbitrary affine numerators, and arbitrary bias. Indeed, near zero $1+tc_{h0}\neq0$ and

$$ \frac1{1+tC_h(x)}=\frac1{1+tc_{h0}}-\sum_{i=1}^n\frac{tc_{hi}}{1+tc_{h0}}\frac{x_i}{1+tC_h(x)}. $$

Write $c_h=(c_{h1},\ldots,c_{hn})$. Define the matrix $J_K(c)$ with rows indexed by nonempty sets $S\subseteq[n]$ of size at most $K$ and columns indexed by pairs $(h,i)$ by

$$ J_K(c)_{S,(h,i)}=\mathbf 1_{i\in S}\prod_{j\in S\setminus\lbrace i\rbrace}c_{hj}. $$

Equivalently, its column $(h,i)$ evaluates the derivative $\partial_i$ at $c_h$ on squarefree monomials of degrees one through $K$.

## The low-degree limit theorem

**Theorem 1.** Suppose $1\leq K\leq n$ and $J_K(c)$ has column rank $nH$. If $t_\nu\gt0$ tends to zero and $g_\nu\in V_C(t_\nu)$ converges as a table to $g$, then $g\in\mathcal P_K$. There are constants $M\gt0$ and $t_0\gt0$, depending on the fixed directions, such that every $g\in V_C(t)$ and every $0\lt t\lt t_0$ satisfy

$$ \max_{|S|\gt K}|\widehat g(S)|\leq Mt\max_{x\in X}|g(x)|, $$

where $\widehat g(S)$ denotes the coefficient of $x^S$ in the multilinear polynomial of the table. The assertion includes arbitrary cancellation and arbitrary scale-dependent numerator coefficients.

**Proof.** Let $M(t)$ be the Boolean monomial coefficient matrix of the $nH$ nonconstant generators $x_i/(1+tC_h(x))$. For a nonempty row $S$ of size $s$, expand at zero:

$$ \frac{x_i}{1+tC_h(x)}=\sum_{k\geq0}(-t)^k x_i C_h(x)^k. $$

Reduction by the Boolean relations cannot increase degree. Hence the coefficient of $x^S$ vanishes at orders below $s-1$. At order $s-1$, it is zero if $i\notin S$; if $i\in S$, all other $s-1$ variables must occur once. Therefore

$$ M_{S,(h,i)}(t)=t^{s-1}\left((-1)^{s-1}(s-1)!J_K(c)_{S,(h,i)}+O(t)\right). $$

The same formula without the notation $J_K$ applies to rows of every degree. Constant terms $c_{h0}$ do not affect the displayed leading coefficient.

Choose $nH$ independent rows $I$ of $J_K(c)$, and write $d_S=|S|$ for their degrees. The corresponding square block factors exactly as

$$ M_I(t)=D_I(t)Q_I(t),\qquad D_I(t)=\mathrm{diag}_{S\in I}(t^{d_S-1}), $$

where $Q_I(t)$ is real analytic near zero and $Q_I(0)$ is invertible. Its inverse is consequently bounded on a sufficiently short positive interval. Every generator vanishes at the zero vertex. Thus if $g=b+M(t)a$ as a table, then $b=g(0)$, and its nonempty coefficient vector $y$ obeys

$$ a=Q_I(t)^{-1}D_I(t)^{-1}y_I. $$

Each selected degree is at most $K$. The coefficients $y_I$ are bounded by $2^n\max_X|g|$, by the Boolean inclusion-exclusion formula. For any row $S$ of degree $s\gt K$, the full matrix formula gives

$$ y_S=t^{s-1}Q_S(t)Q_I(t)^{-1}D_I(t)^{-1}y_I. $$

Every resulting power of $t$ has exponent at least $s-K\geq1$. The remaining analytic factors are bounded. There are finitely many rows, so one constant $M$ gives the claimed inequality. Taking a convergent sequence of tables makes every coefficient of degree above $K$ tend to zero. Thus the limit lies in $\mathcal P_K$. $\blacksquare$

This proof also shows that every first nonzero table coefficient of every nonzero meromorphic score germ in these spaces lies in $\mathcal P_K$: multiply the score by the appropriate positive power of $t$ to obtain a bounded, nonzero limit. No bound on its vanishing or pole order is needed.

**Uniform extension.** Let $\mathcal C$ be a compact set of affine direction configurations such that $J_K(c)$ has full column rank at every configuration in $\mathcal C$. Then the constants $M$ and $t_0$ in Theorem 1 can be chosen uniformly over $\mathcal C$. Therefore its limit conclusion also holds for arbitrary varying configurations $C_\nu\in\mathcal C$ and arbitrary bounded scores $g_\nu\in V_{C_\nu}(t_\nu)$ as $t_\nu\to0$.

To prove this, each configuration has a maximal minor nonzero on a neighborhood. Shrink that neighborhood so the minor is bounded away from zero. The rescaled matrix entries $Q_S(t)$ above depend continuously on both the directions and scale, including at zero. On the closure of a sufficiently small neighborhood, the inverse of its selected square block remains uniformly bounded for a common short interval. Compactness supplies finitely many such neighborhoods. Taking the largest estimate constant and smallest positive interval proves the claim. Compactness also bounds all direction coefficients, so all denominators are uniformly positive on a sufficiently short interval.

## Hamming stars certify a nonempty generic set

**Theorem 2.** Put $q=\lceil\log_2(n+1)\rceil$ and $Q=2^q$. If

$$ HQ\leq D_{K-1}, $$

then $J_K(c)$ has full column rank on a nonempty Zariski-open subset of $(\mathbb R^n)^H$. This open set intersects the strictly positive orthant. In particular, it includes admissible coherent positive-slope radial directions.

**Proof.** Give the $n$ coordinate positions distinct nonzero labels $\alpha_i\in\mathbb F_2^q$, and color each Boolean vector $v$ by its syndrome $\sum_i v_i\alpha_i$. Two distinct vectors of the same color differ in at least three positions: a one-position difference has nonzero syndrome, and a two-position difference has syndrome $\alpha_i+\alpha_j\neq0$.

There are $Q$ colors. Among all $D_{K-1}$ Boolean vectors of weight at most $K-1$, one color contains at least $D_{K-1}/Q$ vectors. Choose $H$ of them as $v_1,\ldots,v_H$. Their closed Hamming stars, consisting of the center and its $n$ neighbors, are pairwise disjoint. Every vertex in those stars has weight at most $K$.

Evaluation on the lower Hamming ball of radius $K$ is an isomorphism from $\mathcal P_K$ to all real tables on that ball. Indeed, both sides have dimension $D_K$, and the matrix of squarefree monomials on subset-indexed vertices is triangular under a linear extension of inclusion, with diagonal entries one.

For a multilinear polynomial $P$ and a Boolean vector $v$,

$$ \partial_iP(v)=(-1)^{v_i}\bigl(P(v\mathbin\oplus e_i)-P(v)\bigr). $$

Since the stars are disjoint, these $nH$ derivative functionals on $\mathcal P_K$ are independent. To isolate a chosen functional, prescribe value one at its unique leaf and zero at every other vertex of the lower Hamming ball, then use the interpolation isomorphism. The resulting derivative is zero at every other selected center-coordinate pair and is one or negative one at the chosen pair. Derivatives kill constants, so the same independence holds on the span of nonconstant monomials. Consequently $J_K(v)$ has rank $nH$.

Some maximal minor is therefore a nonzero polynomial in the direction coordinates. Its nonvanishing set is a nonempty Zariski-open set on which the rank remains full. Perturb every zero coordinate of the selected Boolean vectors to a sufficiently small positive number, leaving their one coordinates fixed. Continuity keeps this minor nonzero and makes every slope strictly positive. $\blacksquare$

## Weak signs handle vanishing leading coordinates

For $F:X\to\lbrace-1,+1\rbrace$, a nonzero table $P\in\mathcal P_K$ is a weak sign representation if $F(x)P(x)\geq0$ for every vertex. Nonzero means not identically zero on the cube.

**Corollary 3.** Fix directions satisfying the rank hypothesis of Theorem 1. If $F$ has no nonzero weak sign representation in $\mathcal P_K$, then there exists $t_F\gt0$ such that no table in $V_C(t)$ strictly represents $F$ for $0\lt t\lt t_F$.

**Proof.** Otherwise choose a sequence $t_\nu\to0$ and strict representing scores $g_\nu\in V_C(t_\nu)$. Scale each score by a positive number so that $\max_X|g_\nu|=1$. The finite-dimensional compact cube of normalized tables contains a convergent subsequence. Its limit $g$ has maximum absolute value one and satisfies $F(x)g(x)\geq0$ at every input. Theorem 1 puts this nonzero table in $\mathcal P_K$, a contradiction. $\blacksquare$

The uniform extension gives the same exclusion uniformly over any compact set $\mathcal C$ of full-rank directions. More precisely, if $C_\nu$ stays in a fixed compact set, $t_\nu\to0$, and $F$ admits strict representations in $V_{C_\nu}(t_\nu)$, then every accumulation point of the configurations belongs to the rank-deficient algebraic set $\lbrace C:\mathrm{rank}J_K(c)\lt nH\rbrace$. Otherwise a convergent subsequence around a full-rank accumulation point would lie in a compact full-rank neighborhood and contradict the same normalized-table argument. This conclusion assumes that $F$ has no nonzero weak representative in $\mathcal P_K$.

The use of weak signs is essential. A leading table can vanish on coordinates whose eventual signs are decided at higher order. The corollary never assumes that a single leading coefficient strictly realizes all labels.

For example, full parity has weak threshold degree $n$. Its correlation with every polynomial of degree below $n$ is zero. A nonzero weak sign representative of lower degree would make that correlation strictly positive, since every summand is nonnegative and at least one is positive. Thus Corollary 3 excludes parity for every generic family furnished by Theorem 2 with $K\lt n$.

There is also a typical-target statement. Anthony's Theorem 1 and Section 6 show that a uniformly random Boolean function has weak threshold degree between $\lfloor n/2\rfloor$ and $\lceil n/2\rceil$, except with probability at most $\exp(-c2^{n/2}/n)$ for an absolute positive constant and all sufficiently large $n$. Section 6 obtains the weak version through parity duality. This is an external theorem used only for the following corollary, not for Theorems 1 and 2. [Primary paper](https://arxiv.org/pdf/2610.15057).

**Corollary 4.** Set $K=\lfloor n/2\rfloor-1$. If $HQ\leq D_{K-1}$, then every direction configuration satisfying the generic rank condition has the following property: except for the probability just stated, a uniformly random target has no strict representation in $V_C(t)$ for all sufficiently small positive $t$. The required smallness threshold can depend on the target and directions. The good event for the random target, namely weak degree at least $\lfloor n/2\rfloor$, works simultaneously for every such direction configuration.

Since $Q\lt2(n+1)$ and $D_{\lfloor n/2\rfloor-2}/2^n\to1/2$, the size condition holds, for example, whenever $H\leq2^n/(16(n+1))$ and $n$ is sufficiently large. Thus this generic fixed-direction radial regime has an obstruction at the scale $2^n/n$, even allowing completely arbitrary moving numerator coefficients and bias.

## Exact remaining gap

The limit theorem controls scales sufficiently close to zero relative to a fixed direction configuration. Its constants depend on an inverse derivative-interpolation matrix. They can diverge as directions approach the rank-deficient algebraic set. An unrestricted representation can approach that set while the scale also varies. At a fixed positive scale, generic perturbations preserve a strict truth table, so genericity alone provides no global restriction.

In particular, one cannot write arbitrary denominators as $1+tC_h$ with a small $t$ and invoke this theorem: doing so changes $C_h$ with $t$, exactly where the fixed-direction control is absent. Nor is a nonconstant common base covered here. The quantitative matrix estimate suggests studying distance to interpolation degeneracy, but no sign-count estimate for all such degenerations has been proved.

## Verification record

Theorems 1 and 2 and Corollary 3 have complete elementary written proofs above. The generic-rank witness is a uniform construction, not a floating-point experiment. Corollary 4 additionally uses the cited external weak-threshold-degree theorem. These results have not been formalized in Lean. They do not establish any improved unrestricted head lower bound.
