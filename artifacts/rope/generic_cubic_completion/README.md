# Generic cubic poles and squarefree completion

## Scope

This note gives a mathematical closure obstruction for the *cubic coefficients of cleared three-head scores*. It also gives an exact fourteen-coordinate pure-atom instance meeting the hypotheses. It does not give a Boolean head-count separation: another polynomial with different cubic coefficients may have the same Boolean signs. The mathematical arguments in this note are not claimed to be Lean-formalized. The accompanying `verify.py` checks the finite rational mass and matrix-minor certificates.

Unlike the earlier product-of-three-forms obstruction, the target here uses six independent linear forms. Its raw cubic can consequently be recovered from its squarefree coefficients, even when a competing representation has unrelated, untied coordinate parameters.

## The only completely split hyperplane sections

Consider the homogeneous cubic in six independent variables

$$ P=x_1y_2y_3+x_2y_1y_3+x_3y_1y_2. $$

The only hyperplanes on which its restriction is a product of three real linear forms are $y_1=0$, $y_2=0$, and $y_3=0$. Here a zero polynomial is excluded; no hyperplane restriction of $P$ is identically zero.

**Proof.** First suppose the hyperplane equation involves an $x$ variable. After relabeling, eliminate $x_1$ by writing

$$ x_1=a_2x_2+a_3x_3+L(y). $$

The restricted polynomial has degree one in $(x_2,x_3)$. If it were a product of three linear forms, exactly one factor would involve these variables. The other two factors would depend only on $y$. Their product would divide both quadratic coefficients of $x_2$ and $x_3$:

$$ y_3(y_1+a_2y_2),\qquad y_2(y_1+a_3y_3). $$

These two nonzero quadratics are not proportional: the first has a nonzero $y_1y_3$ coefficient, while the second has none. Thus no quadratic can divide both.

Now suppose the hyperplane involves only $y$. After restriction the three $x$ variables remain independent and the $y$ variables span a two-dimensional space. The same degree argument would require the three quadratic coefficients $y_2y_3,y_1y_3,y_1y_2$ to be proportional. If none of the restricted $y_i$ vanishes, cancellation in the polynomial ring makes all three restricted linear forms proportional, contrary to their two-dimensional span. Therefore one $y_i$ vanishes, giving one of the three stated hyperplanes. The polynomial has no linear divisor: a hyperplane involving $x$ leaves the two displayed nonzero coefficients, while a hyperplane involving only $y$ leaves at least one nonzero coefficient. $\blacksquare$

The same classification holds when the six forms are independent linear forms in a larger space. A hyperplane involving a direction outside their span leaves all six forms independent after restriction, so it cannot produce a completely split cubic.

## Closure obstruction for mixed poles

Let $U_1,U_2,U_3,B_1,B_2,B_3$ be independent real linear forms in fixed coordinates, with each $B_h$ having both a positive and a negative coordinate coefficient. Define

$$ P=U_1B_2B_3+U_2B_1B_3+U_3B_1B_2. $$

Then $P$ lies outside the coefficientwise closure of cubics

$$ Q=N_1D_2D_3+N_2D_1D_3+N_3D_1D_2 $$

whose three denominator directions each have strictly uniform coordinate signs. Zero denominator directions do not change this conclusion.

**Proof.** Absorb signs into numerator forms so that all denominator coefficients are positive, and normalize each denominator by requiring that its coefficients sum to one. These forms lie in a compact simplex. If a sequence of such cubics converged to $P$, pass to a subsequence on which the three normalized denominators converge to nonzero forms $D_h$ with nonnegative coefficients.

For the vector $v=(1,\ldots,1)$, use the projections

$$ \pi_{h,r}(z)=z-D_{h,r}(z)v. $$

They converge to the analogous projection onto the kernel of $D_h$. On each such hyperplane, the cleared cubic is a product of three linear forms, since the two terms containing $D_{h,r}$ vanish. Products of three linear forms form a closed cone in the finite-dimensional cubic coefficient space: normalize the three factors to unit coefficient norm, use compactness, and absorb their scalar magnitudes into one coefficient. The norm of a product of three unit linear forms has a positive minimum, since a polynomial ring has no zero divisors. This also handles unbounded numerator factors and collisions among denominator limits.

Thus $P$ restricted to the kernel of $D_h$ is completely split, unless it is zero. The preceding classification excludes zero and forces $D_h$ to be proportional to one of the three $B_j$. That is impossible because $D_h$ has nonnegative coefficients and every $B_j$ is mixed. A zero denominator direction in an approximating cubic can first be replaced by an arbitrarily small positive direction; for each fixed numerator list, continuity makes the resulting coefficient change arbitrarily small. $\blacksquare$

The readout threshold in a three-head cleared cubic can be absorbed into one numerator. The cubic homogeneous part depends on at most six linear forms, even when some numerator or denominator directions vanish. Consequently this obstruction applies to all vanilla-admissible three-head cleared cubic homogeneous parts.

## Recovering repeated-index coefficients

A homogeneous cubic has *essential dimension at most six* if it is a cubic polynomial in at most six linear forms. Every Hessian of such a cubic has rank at most six.

Let $P$ be such a cubic in $n\geq 14$ variables. Suppose that, for every distinct coordinate pair $i,k$, the Hessian $H_P(e_k)$ has a nonsingular six-by-six cross submatrix on disjoint index sets $A,B$ avoiding both $i$ and $k$.

Then the squarefree cubic coefficients determine $P$ uniquely among all cubics of essential dimension at most six. They also determine it continuously near $P$ within that class.

**Proof.** Write $M=H_Q(e_k)$ for a competing cubic. Every entry of the cross block $M_{A,B}$, the row $M_{i,B}$, and the column $M_{A,i}$ is a squarefree cubic coefficient, because the three indices involved are distinct. Rank at most six and invertibility of the cross block imply the Schur identity

$$ M_{ii}=M_{i,B}(M_{A,B})^{-1}M_{A,i}. $$

Indeed, the six rows indexed by $A$ are independent and span the row space; restriction to columns $B$ determines the row coefficients. This recovers every coefficient of $x_i^2x_k$ for $i\neq k$. Once these are known, every off-diagonal entry of each $H_Q(e_k)$ is known, including entries involving $k$. A further disjoint six-by-six cross block avoiding $k$ recovers $M_{kk}$ and hence the coefficient of $x_k^3$ by the same identity.

For a sequence of squarefree coefficient tensors converging to those of $P$, the chosen cross determinants remain nonzero. The displayed rational formulas then recover all remaining coefficients continuously. $\blacksquare$

Combining this with the mixed-pole closure obstruction shows that a target meeting both hypotheses has squarefree cubic coefficients outside the closure of all vanilla three-head cubic coefficient tensors. This statement permits arbitrary untied vanilla parameters. It is still a coefficient obstruction, not a sign obstruction.

## An exact fourteen-coordinate pure instance

For $i\in\lbrace1,\ldots,14\rbrace$ and $h\in\lbrace0,1,2\rbrace$, put

$$ s_{h,i}=\frac{i^h}{10^4},\qquad b_{h,i}=\frac{i^{h+3}-(15/2)^{h+3}}{10^9}. $$

Every $s_{h,i}$ is strictly greater than $|b_{h,i}|$, each row sum of $s$ is less than one, and each row of $b$ has both signs. The following are exact pure scalar atom parameters, with centered input coordinates $z_i=2x_i-1$:

$$ a_{h,i}=s_{h,i}-b_{h,i},\quad \widehat b_{h,i}=s_{h,i}+b_{h,i},\quad \gamma_h=1-\sum_i s_{h,i},\quad \eta_h=-\sum_i b_{h,i},\quad v_{0,h}=-1,\quad v_{1,h}=1. $$

Their scores are exactly $S_h(z)/(1+B_h(z))$, where $S_h=\sum_i s_{h,i}z_i$ and $B_h=\sum_i b_{h,i}z_i$. The cubic homogeneous part of their cleared sum is

$$ P=S_0B_1B_2+S_1B_0B_2+S_2B_0B_1. $$

The six forms are independent. In fact, the matrix with row $i$ equal to $(s_{0,i},s_{1,i},s_{2,i},b_{0,i},b_{1,i},b_{2,i})$ is an invertible change of basis and scaling of a six-column Vandermonde matrix. Every six-row minor is nonzero.

For the universal cubic, its Hessian at a point with denominator coordinates $\beta_0,\beta_1,\beta_2$ has determinant

$$ -4(\beta_0\beta_1\beta_2)^2. $$

None of the $b_{h,k}$ vanishes. Therefore every required cross Hessian minor is a product of two nonzero Vandermonde minors and a nonzero universal Hessian determinant. The verifier checks all 42 mass inequalities, all 3003 six-row Vandermonde minors, and all 182 chosen cross Hessian minors using exact rational arithmetic.

The scalar atom construction is also available generally as `HeadComplexity.PureRoPECenteredConstruction.atom_eval`. Realization by the specified fixed-query, token-only-value pure RoPE architecture uses the finite-position scalar-to-rotation bridge in `theorems/03_rotary_attention/014_rope_head_complexity.md`.

## Exact remaining Boolean gap

The construction supplies a pure cubic coefficient tensor that all three-head vanilla coefficient tensors avoid, even in closure. It does not show that the Boolean sign function of the displayed pure score lacks a different three-head vanilla representation. To obtain a Boolean separation, one must force every strict cubic sign certificate for a finite truth table into the excluded coefficient neighborhood, or supply another all-admissible sign argument. Neither has been established here.
