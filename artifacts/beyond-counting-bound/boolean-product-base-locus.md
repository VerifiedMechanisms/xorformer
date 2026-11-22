# Boolean Product Base Loci

## Scope

This note audits the degree of a product of affine Boolean evaluation tables. It proves the complete two-factor base-locus classification and an eight-to-one complex factorization statement on three bits. Neither theorem is a lower bound for head complexity. In particular, generic complex factorization counts do not count admissible real sign patterns.

## Theorem 1. Two-factor classification

Let $K$ be a field of characteristic zero, and let $A,B$ be nonzero affine polynomials in $n\geq1$ variables. Their product vanishes at every vertex of $\lbrace0,1\rbrace^n$ if and only if, after interchanging the factors and multiplying each by a nonzero scalar, their unordered pair is one of

$$ \lbrace x_i,1-x_i\rbrace\qquad\text{or}\qquad\lbrace x_i-x_j,1-x_i-x_j\rbrace\quad(i\lt j). $$

Consequently, the product map from $\mathbb P^n\times\mathbb P^n$ has exactly $n(n+1)$ ordered base points.

**Proof.** Write $A=a_0+\sum_i a_ix_i$ and $B=b_0+\sum_i b_ix_i$. Evaluation at the origin gives $a_0b_0=0$. The two constants cannot both vanish: otherwise singleton evaluations give $a_ib_i=0$, and evaluation at $e_i+e_j$, for indices with $a_i\neq0$ and $b_j\neq0$, gives the contradiction $a_ib_j=0$. Interchange the factors so that $a_0=0$, and rescale $B$ so that $b_0=1$.

Singleton and two-coordinate evaluations now give

$$ a_i(1+b_i)=0,\qquad a_ib_j+a_jb_i=0\quad(i\neq j). $$

Let $T=\lbrace i:a_i\neq0\rbrace$. It is nonempty. For $i\in T$, the first identity gives $b_i=-1$. For $j\notin T$, the second identity, using any $i\in T$, gives $b_j=0$. For distinct $i,j\in T$, the second identity gives $a_i+a_j=0$. Three distinct members of $T$ would therefore force $2a_i=0$, a contradiction. If $|T|=1$, the factors have the first stated form. If $T=\lbrace i,j\rbrace$, they have the second form. Direct substitution on the cube proves both converses. The listed unordered pairs are distinct, and their two factors are never proportional, so the ordered count is $2n+2\binom n2=n(n+1)$. $\blacksquare$

The real normalized classification and the impossibility of two zero constant terms are kernel checked in `HeadComplexity.BooleanZeroProduct.normalized_classification` and `HeadComplexity.BooleanZeroProduct.nonzero_constant_needed`. The written field argument also applies over the complex numbers; that extension is not claimed as a Lean declaration.

## Theorem 2. Reduced base points

Every base point in Theorem 1 is reduced, and the derivative of the evaluation sections has rank $2n$ on its projective tangent space.

**Proof.** The derivative at $(A,B)$ sends $(\dot A,\dot B)$ to the table

$$ x\longmapsto B(x)\dot A(x)+A(x)\dot B(x). $$

For either listed pair, the zero sets of $A$ and $B$ partition the Boolean vertices. Each zero set affinely spans its defining hyperplane. On the zeros of $A$, the multiplier $B$ is nonzero, so a zero derivative forces $\dot A$ to vanish there. Hence $\dot A$ is proportional to $A$. Similarly, $\dot B$ is proportional to $B$. These are precisely the two scaling directions removed in the projective tangent space. The derivative is therefore injective on a space of dimension $2n$.

In a local affine chart of the smooth product of projective spaces, the evaluation sections consequently span the cotangent space at the base point. Their ideal equals the maximal ideal by Nakayama's lemma. Thus the base scheme is reduced there. $\blacksquare$

## Theorem 3. Eight generic ordered factorizations on three bits

Over $\mathbb C$, the rational map

$$ \Phi:\mathbb P^3\times\mathbb P^3\dashrightarrow\mathbb P^7,\qquad([A],[B])\longmapsto[A(x)B(x)]_{x\in\lbrace0,1\rbrace^3} $$

has image a projective hyperplane and has eight distinct points in a generic fiber. Thus a generic table in its image has four unordered affine factorizations.

**Proof.** Boolean reduction of $AB$ has degree at most two. Its coefficient of $x_1x_2x_3$ is zero, so its eight values satisfy one fixed linear relation. The image lies in the resulting $\mathbb P^6$.

To prove dominance onto this hyperplane, use the chart $A=1+\sum_i a_ix_i$, $B=1+\sum_i b_ix_i$. The six nonconstant reduced coefficients are

$$ \ell_i=a_i+b_i+a_ib_i,\qquad q_{ij}=a_ib_j+a_jb_i. $$

At $a=(1,2,3)$ and $b=(4,5,7)$, their Jacobian, with rows ordered as $\ell_1,\ell_2,\ell_3,q_{12},q_{13},q_{23}$ and columns as $a_1,a_2,a_3,b_1,b_2,b_3$, is

$$ J=\begin{pmatrix}5&0&0&2&0&0\cr0&6&0&0&3&0\cr0&0&8&0&0&4\cr5&4&0&2&1&0\cr7&0&4&3&0&1\cr0&7&5&0&3&2\end{pmatrix},\qquad\det J=-24. $$

The image therefore has dimension six and is the whole hyperplane after closure. Its generic fiber is finite.

Six generic hyperplanes in that target $\mathbb P^6$ cut out a generic point. Pulling them back gives six divisors of bidegree $(1,1)$ on $\mathbb P^3\times\mathbb P^3$. Their common zero set consists of the finite generic fiber and the twelve base points. At every base point, six generic combinations of the evaluation sections have independent differentials by Theorem 2, so its intersection multiplicity is one. The multihomogeneous intersection number is

$$ \mathrm{coeff}_{u^3v^3}\bigl((u+v)^6\bigr)=\binom63=20. $$

Hence the generic fiber has total multiplicity $20-12=8$. In characteristic zero the generically finite map is generically separable, so these eight points are distinct for a generic target. The factor-swap involution has no fixed point in a generic fiber: equal factors form a three-dimensional subset of the six-dimensional source. Dividing these eight points into pairs gives four unordered factorizations. $\blacksquare$

The multihomogeneous intersection calculation is the usual divisor version of Bezout's theorem; see [Heintz, Jeronimo, Sabia and Solerno, Section 2.1](https://mate.dm.uba.ar/~jeronimo/papers/HJSS05.pdf). The proof above checks finiteness and the base-point multiplicities separately, rather than treating the evaluation sections as generic bilinear forms.

## Theorem 4. Positive factorization ambiguity

For every $n\geq1$, one fixed Boolean product table has at least $n+1$ distinct unordered factorizations into affine forms with constant term one and strictly positive slopes. On three bits, four such unordered factorizations are regular and persist for every table in an open neighborhood in the quadratic-table hyperplane.

**Proof.** Put $t(x)=\sum_i x_i$. The starting factors are $A_0=1+2t$ and $B_0=1+3t$. For each coordinate $i$, put

$$ A_i=1+2t-x_i/3,\qquad B_i=1+3t+x_i/2. $$

The exact polynomial identity

$$ (1+2t-x/3)(1+3t+x/2)=(1+2t)(1+3t)+(x-x^2)/6 $$

shows that $A_iB_i=A_0B_0$ on the cube. Each $A_i$ has slopes two except for the slope $5/3$ at coordinate $i$; each $B_i$ has slopes three except for $7/2$ there. All slopes and constant terms are strictly positive. The first factors are pairwise distinct, the second factors are pairwise distinct, and no first factor equals a second factor. Their constant terms exclude nontrivial projective rescaling. This gives $n+1$ distinct unordered pairs.

For three bits, all four pairs have reduced coefficient vector

$$ (\ell_1,\ell_2,\ell_3,q_{12},q_{13},q_{23})=(11,11,11,12,12,12). $$

Using the Jacobian formula in Theorem 3, its determinant at the uniform pair is $2$, and its determinant at each of the other three pairs is $-23/3$. All four points are regular. Take disjoint neighborhoods of these parameter points, small enough that every slope remains positive. The inverse function theorem supplies an open image neighborhood from each; their finite intersection is an open neighborhood on which the four distinct unordered positive factorizations persist. $\blacksquare$

The scalar exchange identity, its Boolean specialization, positivity of the displayed slopes, and injectivity of the first-factor coefficient vectors are Lean checked in `BooleanZeroProduct.lean`. The analytic open-neighborhood assertion and the three-bit generic degree calculation remain written proofs, not Lean declarations.

## Literature audit and remaining gap

The [Hadamard-product degree formulas of Bocci, Carlini and Kileel](https://web.ma.utexas.edu/users/jkileel/HadamardPublished.pdf) require their stated genericity and fiber hypotheses. The three-bit computation shows why a direct division by the factor-permutation count is insufficient for Boolean evaluation spaces. The two-factor calculation gives no uniform degree estimate for exponentially many factors.

[Sauermann and Xu](https://arxiv.org/abs/2310.05775) prove a lower bound of order $n^{2/3}/(\log n)^{2/3}$ for essential hyperplane covers of the cube, and a linear lower bound for skew covers. These constrain vanishing products. The positive denominator products in the manuscript have no Boolean zeros, and an arbitrary cleared numerator is a sum of products. No implication from those covering bounds to a count of its coordinate signs has been established here.

[Clarke, Dewar, Gallet, Grasegger, Green Tripp and Smith, Theorem 1.3](https://arxiv.org/html/2511.22646v1) identify a matroid flip product with the generic ambient fiber count for a product of two linear spaces. Their finite nonzero case requires the two ranks to sum to the ambient coordinate count plus one. The theorem is not a fiber theorem over every proper product image, and a product of several linear spaces is generally nonlinear. [Antolini, Dewar and Tanigawa](https://arxiv.org/html/2508.04798v1) explicitly disprove the naive extension of the two-factor algebraic-matroid formula to three or more factors.

[Briand, Kayser and Weigert, Theorem A](https://arxiv.org/html/2606.26281v1) compute polar degrees of a reciprocal linear space from its reduced matroid characteristic polynomial. This is a precise new tool for one reciprocal variety. It does not provide polar degrees or a coordinate-sign bound for the sums of arbitrary affine-ratio heads required here.

The route is blocked at a bound for the actual coordinate sign tests of the many-head tangent family. Neither the base-point classification nor the cited matroid formulas imply such a bound. The main target and any proposed lower bound with a denominator exponent strictly between one and two remain unproved.
