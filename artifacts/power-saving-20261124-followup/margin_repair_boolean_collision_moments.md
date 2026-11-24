# Boolean collision moments and the ordinary moment gap

## Exact scope

This note isolates what a common-base collision actually implies about its direction parameters. The squarefree and tangent moment deductions below are written proofs. The six-point counterexample is kernel checked in `formalization/HeadComplexity/Research/BooleanProjectionMomentAliasing.lean`.

The counterexample is an identically zero six-head score, not a truth table with universally small margin. Its role is to rule out a proposed inference about collision moments. Every displayed reciprocal head is admissible in the original model.

## What vanishing Taylor coefficients imply

First consider a cluster with fixed constant residues, fixed affine directions, and a common positive affine base:

$$ S_\varepsilon(x)=\sum_{h=1}^H\frac{c_h}{B(x)+\varepsilon D_h(x)},\qquad D_h(x)=a_h+\sum_{i=1}^n w_{hi}x_i. $$

For sufficiently small $\varepsilon$, its Taylor coefficient of order $q$ at each cube point is

$$ (-1)^q B(x)^{-q-1}m_q(x),\qquad m_q(x)=\sum_h c_hD_h(x)^q. $$

Thus vanishing of that coefficient on the entire cube is equivalent to vanishing of $m_q$ as a function on the Boolean cube. It is not equivalent to vanishing as an ordinary polynomial on real input space.

For a coordinate set $T$ of size $q$, apply the Boolean coefficient functional

$$ \Delta_Tg=\sum_{U\subseteq T}(-1)^{|T|-|U|}g(\mathbf1_U). $$

To compute $\Delta_T D_h^q$, expand the product of $q$ copies of $D_h$. Terms missing any coordinate of $T$ cancel. A surviving term must use every coordinate exactly once and cannot use the constant term. There are $q!$ orderings. Hence

$$ \Delta_T D_h^q=q!\prod_{i\in T}w_{hi}. $$

It follows that cancellation through orders $0,\ldots,r$ gives exactly the following useful necessary constraints:

$$ \sum_h c_h\prod_{i\in T}w_{hi}=0\qquad (|T|\leq r). $$

In particular, cancellation through order $n$ gives a linear dependence of the Segre evaluation vectors

$$ v(w_h)=\left(\prod_{i\in T}w_{hi}\right)_{T\subseteq[n]}. $$

This does not establish the analogous identities for arbitrary repeated-coordinate monomials.

For fixed affine numerators $A_h(x)=b_h+\sum_i u_{hi}x_i$, the Taylor numerator instead is $\sum_h A_hD_h^q$. Its coefficient on a set $T$ of size $q+1$ is

$$ q!\sum_h\sum_{i\in T}u_{hi}\prod_{j\in T\setminus\lbrace i\rbrace}w_{hj}. $$

Consequently vanishing through order $n-1$ gives the sum of the corresponding tangent vectors to the Segre map equal to zero. This statement concerns fixed numerators. If the numerator coefficients also depend on $\varepsilon$, different orders mix, and these pure moment identities need not hold separately.

## A kernel-checked obstruction to full moments

Take the positive direction clouds

$$ P=\lbrace(3,2),(2,1),(1,3)\rbrace,\qquad Q=\lbrace(1,2),(3,1),(2,3)\rbrace. $$

For each $x\in\lbrace0,1\rbrace^2$, the multisets $\lbrace p\cdot x:p\in P\rbrace$ and $\lbrace q\cdot x:q\in Q\rbrace$ coincide. At the four inputs, both are respectively $\lbrace0,0,0\rbrace$, $\lbrace1,2,3\rbrace$, $\lbrace1,2,3\rbrace$, and $\lbrace3,4,5\rbrace$.

Therefore, for every scalar function $F$, every real $a,\varepsilon$, and every Boolean $x$,

$$ \sum_{p\in P}F(a+\varepsilon p\cdot x)=\sum_{q\in Q}F(a+\varepsilon q\cdot x). $$

This is `scalar_function_identity`. Choosing powers gives `all_projection_moments` for every natural order, with no upper bound. Nevertheless,

$$ \sum_{p\in P}p_1^2p_2-\sum_{q\in Q}q_1^2q_2=2,\qquad \sum_{p\in P}p_1p_2^2-\sum_{q\in Q}q_1q_2^2=-2. $$

These are `mixed_moment_21_difference` and `mixed_moment_12_difference`. Before restriction to the cube, the cubic discrepancy is

$$ \sum_{p\in P}(p_1s+p_2t)^3-\sum_{q\in Q}(q_1s+q_2t)^3=6st(s-t). $$

The declaration `cubic_projection_difference` verifies this polynomial identity. The right side vanishes on Boolean inputs because

$$ st(s-t)=(s^2-s)t-s(t^2-t). $$

For every $\varepsilon\gt0$, choose $F(t)=1/t$ and $a=1$. The three positive and three negative heads have numerators $+1$ and $-1$, denominator intercept one, and strictly positive denominator slopes $\varepsilon p_i$ or $\varepsilon q_i$. The declaration `six_genuine_heads_cancel` proves that their sum is identically zero on the full cube. The atom constructors, and therefore admissibility, are part of the kernel-checked statement.

## The failed inference and the remaining interface

The following implication is false, even with positive directions and cancellation at every order:

$$ \left[\forall q\geq0,\forall x\in\lbrace0,1\rbrace^n,\sum_h c_hD_h(x)^q=0\right]\Longrightarrow\left[\forall\alpha,\sum_h c_hw_h^\alpha=0\right]. $$

Thus ordinary point-set Hilbert-function interpolation cannot be applied merely by calling the Taylor coefficients multivariate moments. The Boolean vanishing ideal must be retained. The example does not rule out a theorem after quotienting exact zero-score identities, nor does it rule out a repair using new denominator directions.

For the constant-residue Segre dependence, a useful necessary condition survives every partition of the coordinates into $A$ and $C$. Let $V_A$ and $V_C$ have columns indexed by the heads and rows indexed by squarefree monomials in their respective coordinate sets. Then

$$ V_A\mathrm{diag}(c)V_C^{\top}=0. $$

After deleting zero residues, the diagonal matrix is invertible, so elementary rank-nullity gives

$$ \mathrm{rank}(V_A)+\mathrm{rank}(V_C)\leq H. $$

The simultaneous constraints over many partitions are stronger than one generic rank defect. Turning them, together with the higher grouped moments, into a count of all low-margin truth tables is still open here. A theorem merely asserting generic independence would not suffice, because the requested bound must include the exceptional parameter strata and arbitrary signed residues.

There is a second algebraic caution. The direction-polynomial spaces $E_q=\mathrm{span}\lbrace(w\cdot x)^q:x\in\lbrace0,1\rbrace^n\rbrace$ are not a multiplicative filtration. In two coordinates, $w_1\in E_1$ and $w_1w_2\in E_2$, whereas $w_1^2w_2\notin E_3$. The last assertion follows either by expanding the four Boolean projections, or by applying the six-point functional above, which annihilates $E_3$ and takes value two on that monomial. Thus a Hilbert-growth theorem for graded algebras cannot be applied directly to the spaces $E_q$. They are dual spaces associated with the Boolean input quotient, not an algebra of direction polynomials.

A related available structural result is the product-tensor splitting theorem: a circuit of $H$ product tensors can vary in at most $H-2$ tensor factors. Its hypotheses apply to a minimal Segre dependence, but the resulting inequality is too weak when $H$ is exponential in $n$. See [Lovitz and Petrov, A generalization of Kruskal's theorem on tensor decomposition, Corollary 21](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/generalization-of-kruskals-theorem-on-tensor-decomposition/515357D904DD4AD1042F37BBCBC95B35). This external theorem is not used by any Lean declaration in this checkpoint.

## A temporary rank plateau after exact ghosts are excluded

Discarding exact zero-score relations does not by itself restore ordinary Veronese interpolation. Consider the seven positive points, with the listed signed residues:

$$ ((1,1),(1,2),(1,3),(2,2),(2,3),(3,1),(3,3)),\qquad c=(1,-4,3,4,-4,-1,1). $$

Their Boolean projection moments vanish through degree three, while their fourth moment is

$$ \sum_h c_h(w_h\cdot x)^4=24x_1x_2\qquad (x\in\lbrace0,1\rbrace^2). $$

These two claims are kernel checked as `plateau_moments_through_three` and `plateau_fourth_moment`. All direction coefficients are strictly positive.

The exact rational computation in `collision_moment_plateau_certificate.py`, with output `collision_moment_plateau_certificate.json`, gives ranks $3,6,6,7$ for the evaluation matrices containing all Boolean projection powers through orders $1,2,3,4$. The quadratic feature rows $1,w_1,w_2,w_1^2,w_1w_2,w_2^2$ have six-column deletion determinants

$$ (-4,-16,-12,16,16,-4,-4). $$

Every deletion is independent, so the seven points form a circuit for the moments through order three. Their affine span has dimension two. They are not an exact ghost, since order four is nonzero. Thus the proposed direct analogue of the ordinary Veronese circuit inequality $H\geq r d+2$, for a circuit annihilating orders through $r$ and having affine span $d$, is false: here $7\lt3\cdot2+2$.

This only refutes that precise inequality. A weaker growth theorem with additional structure or different constants remains possible. Also, the first nonzero Boolean jet here is simply a face indicator, so this example supplies no difficult unrestricted truth table. A successful replacement may have to charge both moment growth and the support of the first nonzero jet.

There is a useful repair of this particular plateau if auxiliary directions are permitted. Subtracting $(1,1)$ from the seven points gives the exponential generating polynomial

$$ P(u,v)=1-4v+3v^2+4uv-4uv^2-u^2+u^2v^2=2(u-1)(v-1)(u-v)+(u-1)^2(v-1)^2. $$

The first summand is the six-point exact ghost. Consequently the seven-point cloud has the same Boolean projections as the nine-point tensor fourth difference represented by $(u-1)^2(v-1)^2$. Restoring the positive translation multiplies both sides by $uv$. The replacement has ordinary vanishing order four at $(1,1)$, as well as Boolean order four. This algebraic identity is an exact written calculation, separate from the Lean declarations above.

The possible general interface is therefore a *sparse filtered lift*: replace an $H$-term exponential sum modulo all exact Boolean-projection ghosts by a sum with $O(H)$ terms whose ordinary order of vanishing is at least its first nonzero Boolean order. The seven-point example neither proves nor refutes such a statement. Auxiliary directions, rather than merely deleting dependent original directions, are necessary even in this example.

This interface only treats straight collisions $B+\varepsilon D_h$ with constant residues. Fixed affine numerators give derivative, or tangent, generators and require a corresponding filtered lift. General parameter paths can have higher-order denominator and numerator coefficients, which mix in the first nonzero score jet. An unrestricted repair theorem would have to control those paths as well, or give an independent reason that straight constant-residue collisions suffice to count all remaining truth tables. No such reduction has been proved here.
