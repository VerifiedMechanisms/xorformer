# Exponential border rank of a canonical cleared numerator

## Statement and scope

For every integer $H\geq1$, there is an admissible original score on $n=4H$ Boolean variables whose canonical cleared numerator has balanced matrix rank

$$ R_H=2^{H+1}-2. $$

Consequently, any sequence of tables made from $K$ affine-times-positive-product atoms and a free bias that converges entrywise to this particular cleared numerator must have $K\geq2^H-1$. Arbitrary real scaling of the whole table is permitted before taking the limit. The general finite-difference compiler attains this border bound.

This is an exact-table and exact-limit statement. It is not a lower bound for sign compilation: the same construction can have a sign representation with one affine-times-positive-product atom and one original head. An arbitrary positive pointwise multiplier or a different sign-equivalent limiting table is outside the conclusion.

## A universal rank upper bound for the cleared polynomial

Split the input coordinates into left variables $y$ and right variables $z$. After absorbing the free score bias into one numerator, write

$$ A_h(y,z)=a_h(y)+a'_h(z),\qquad B_h(y,z)=u_h(y)+v_h(z). $$

The constant terms may be assigned to either side. Let

$$ P(y,z)=\sum_{h=1}^H A_h(y,z)\prod_{g\neq h}B_g(y,z). $$

For $T\subseteq[H]$, define

$$ U_T=\prod_{h\in T}u_h,\qquad M_T=\sum_{h\in T}a_h\prod _{g\in T\setminus\lbrace h\rbrace}u_g. $$

Define $V_T,N_T$ by the same formulas on the right, using $v_h,a'_h$. The empty products are one and $M _{\varnothing}=N _{\varnothing}=0$. Expanding according to which heads contribute left factors gives

$$ P(y,z)=\sum_{T\subseteq[H]}\bigl(M_T(y)V_{T^c}(z)+U_T(y)N_{T^c}(z)\bigr). $$

Exactly $2^H-1$ potentially nonzero rank-one terms occur in each of the two sums. Therefore the left-right evaluation matrix of every such $P$ has rank at most $R_H$.

## An admissible construction attaining the rank

Take $2H$ Boolean coordinates $(a_h,u_h) _{h=1}^H$ on the left and $2H$ Boolean coordinates $(a'_h,v_h) _{h=1}^H$ on the right. First use

$$ A_h=a_h+a'_h,\qquad B_h=1+u_h+v_h. $$

These preliminary denominators have zero slopes on unused coordinates; they will be perturbed below. In the expansion above, use $u_h$ on the left and $1+v_h$ on the right.

The left functions $U_T$ for proper subsets $T\subsetneq[H]$ and $M_T$ for nonempty subsets $T$ are linearly independent as Boolean tables. The $U_T$ are distinct squarefree monomials with no marked $a$ variable. Every $M_T$ is a nonzero sum of monomials with exactly one marked $a$ variable, and the monomial supports belonging to different $T$ are disjoint. All these polynomials are multilinear, so their coefficient independence implies independence of their Boolean evaluation tables.

The analogous right family is also independent. Replacing each $v_h$ by $1+v_h$ is an invertible change of basis in the multilinear polynomial space, so it does not change the independence argument.

In these two independent families, the expansion of $P$ pairs $M_T$ with $V_{T^c}$ for nonempty $T$, and $U_T$ with $N_{T^c}$ for proper $T$. Its coefficient matrix is a permutation matrix of size $R_H$. The evaluation matrix therefore has rank exactly $R_H$.

Now put

$$ B_{h,\varepsilon}=1+u_h+v_h+\varepsilon\sum_{i=1}^{4H}x_i. $$

For every $\varepsilon\gt0$, every denominator slope is strictly positive and the denominator is positive on the entire cube. A nonzero $R_H$ by $R_H$ minor of the preliminary cleared table varies polynomially with $\varepsilon$ and is nonzero at zero. It stays nonzero for all sufficiently small positive $\varepsilon$. The universal upper bound already proved forces equality of the rank. The numerators are arbitrary affine forms and all denominators are nonconstant, so this is an admissible original representation.

If strict score labels are desired, first choose a sufficiently small negative free bias $c$. The preliminary score is zero precisely when all the marked $a_h,a'_h$ bits vanish and is positive otherwise. Its finitely many positive values have positive minimum. Choose $|c|$ below that minimum and small enough to preserve the nonzero cleared minor after bias absorption into $A_1+cB_1$. Then choose $\varepsilon\gt0$ sufficiently small to preserve both the minor and all strict labels. This supplies a strict original-model witness without altering the rank argument.

## Sharpness for exact limiting compilers

A positive product atom splits as a left function times a right function. Multiplying it by an affine form gives a sum of two rank-one matrices, one for the left affine part and one for the right affine part. Thus $K$ affine-times-product atoms and a free bias have evaluation rank at most $2K+1$.

The set of matrices of rank at most $2K+1$ is closed, since all larger minors vanish. Hence every entrywise limit of such tables, including after an arbitrary real scalar rescaling at each step, still has rank at most $2K+1$. To converge to the displayed $P$, it is necessary that

$$ 2K+1\geq2^{H+1}-2,\qquad K\geq2^H-1. $$

Conversely, `general_finite_difference_product_compilation.md` constructs $2^H-1$ affine-times-positive-product atoms whose positive scalar rescalings converge to $P$. This proves sharpness as a border statement. It does not assert an exact finite product representation of $P$ with that many atoms.

## The same labels need only one atom

For the negative bias just chosen, the strict labels are exactly the Boolean OR of the $2H$ marked bits. The sufficiently small coherent perturbation preserves them. They therefore have the strict affine sign representation

$$ L(x)=\sum_{h=1}^H(a_h+a'_h)-\frac12. $$

This is one affine-times-positive-product atom with all product factors equal to one. It is also the numerator of one admissible original head, after division by any strictly positive coherent nonconstant affine denominator.

Thus the exponential lower bound for convergence to this canonical cleared table coexists with a one-head representation of its labels. This explicitly prevents using the matrix-rank obstruction as the requested unrestricted head lower bound or as a general sign-compilation lower bound.

## Verification boundary

This is a written finite-dimensional algebraic proof. No Lean verification or numerical experiment is claimed. The parent independently checked the rank decomposition, independence argument, coherent perturbation, and closed-rank limit argument.
