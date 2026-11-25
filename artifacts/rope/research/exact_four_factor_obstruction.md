# The Source Cubic Has No Exact Oriented Four-Factor Representation

This is a mathematical obstruction for exact polynomial identities and continuous-cube sign representations. It is not a proof that any finite Boolean member of the separating family needs five vanilla heads. The finite-grid limit may involve coalescing denominators and unbounded numerator coefficients, which this argument does not control.

## The polynomial and its six codimension-two zero spaces

Work over the reals with independent linear coordinates $D_1,D_2,D_3,N_1,N_2,N_3$, together with any number of unused coordinates. Homogenization of the physical affine coordinates adds the constant coordinate among these unused coordinates. Let

$$ P=N_1D_2D_3+N_2D_1D_3+N_3D_1D_2. $$

For a two-dimensional space $U$ of linear forms, write $(U)$ for its generated ideal.

**Claim.** The condition $P\in(U)$ holds exactly for the following six spaces:

$$ U=\mathrm{span}(D_i,D_j)\quad(i\neq j),\qquad U=\mathrm{span}(D_i,N_i)\quad(i=1,2,3). $$

**Proof.** Project $U$ onto the space spanned by the numerator and unused coordinates, and let its rank be $r$.

If $r=2$, the two equations defining the zero space can be solved in the outside coordinates while leaving all three denominator coordinates arbitrary. For every denominator vector, the coefficient vector

$$ g(D)=(D_2D_3,D_1D_3,D_1D_2) $$

would then lie in the same two-dimensional row space of outside constraints. Evaluating at denominator vectors $(0,1,1)$, $(1,0,1)$, and $(1,1,0)$ gives three independent coefficient vectors. This is impossible.

If $r=1$, choose the two equations as $\ell(D)=0$ and $A(N,Z)+b(D)=0$, where $Z$ denotes the unused coordinates. On the denominator plane $\ell=0$, all coefficient vectors $g(D)$ must be proportional to the fixed form $A$. Since $g$ has no unused-coordinate component, $A$ has none either.

The restriction of the three quadratics $D_2D_3,D_1D_3,D_1D_2$ to a denominator plane has span at most one only for a coordinate plane. To see this, solve a non-coordinate equation, after permutation, as $D_3=-aD_1-bD_2$, with at least one of $a,b$ nonzero. The restricted quadratics include $D_1D_2$ and a quadratic having a nonzero $D_1^2$ or $D_2^2$ term, so their span has dimension at least two. Thus $\ell$ is proportional to some $D_i$. On this plane, $g$ has only the component indexed by $i$ nonzero. Hence $A$ is proportional to $N_i$. Substitution into $P$ then forces $b$ to vanish on $D_i=0$, so $b$ is proportional to $D_i$. The resulting space is $\mathrm{span}(D_i,N_i)$.

If $r=0$, both constraints involve only denominator coordinates. Their common denominator zero space is a line. Along that line all three pairwise products of denominator coordinates must vanish. The line is therefore a coordinate axis, giving $\mathrm{span}(D_i,D_j)$.

The converse follows immediately from the displayed formula for $P$. $\blacksquare$

**First-order vanishing.** For every one of these six spaces, $P\notin(U)^2$. For $\mathrm{span}(D_i,D_j)$, the terms containing just one of those two denominator coordinates have nonzero coefficients. For $\mathrm{span}(D_i,N_i)$, the whole polynomial has degree exactly one in those two coordinates. Consequently no codimension-two zero space of this cubic is a double zero space.

## The orientation restriction

Return to the physical eighteen-coordinate source. Its denominator slope rows have coordinate sum zero and are independent. A nonzero linear combination of two source denominator forms therefore cannot be a vanilla denominator: strictly uniform slopes would have nonzero coordinate sum, while zero slopes force the combination to be zero. A nonzero constant denominator is also not such a combination.

It follows that if two independent vanilla denominator forms $L_i,L_j$ have $P\in(L_i,L_j)$, then

$$ \mathrm{span}(L_i,L_j)=U_h,\qquad U_h=\mathrm{span}(D_h,N_h) $$

for some $h$. The three spaces $U_1,U_2,U_3$ intersect pairwise only in zero. Both strictly positive and strictly negative slope orientations are covered; nonzero constant denominators are also allowed.

## Four distinct denominator factors

Suppose four pairwise nonproportional vanilla denominator forms satisfy an exact identity

$$ P F=\sum_{i=1}^{4}A_i\prod_{j\neq i}L_j, $$

where the $A_i$ are arbitrary linear forms and $F$ is a nonzero linear form. All forms here are homogenized, so affine numerator corrections, a free score constant, constant denominators, and an affine multiplier are included.

For every pair $i,j$, the right side belongs to $(L_i,L_j)$. This ideal is prime. Therefore either $F\in\mathrm{span}(L_i,L_j)$ or $P\in(L_i,L_j)$. By the preceding section, the latter case means both factors belong to one $U_h$.

The following elementary arrangement lemma applies. If four distinct projective points have this pair property, then either all four lie in a two-dimensional linear space, or three lie in one $U_h$ and the fourth is proportional to $F$ outside that space.

To verify the lemma, first suppose some pair lies in $U_h$. If $F$ also lies in $U_h$, comparison with either member of that pair forces every other point into $U_h$. If $F$ lies outside $U_h$, any point outside $U_h$ must span $F$ with both independent members of the pair; it must therefore be proportional to $F$. There is at most one such point. If no pair lies in a common $U_h$, every pair spans $F$. Choosing any pair shows that every point lies in its two-dimensional span.

If all four factors lie in a two-dimensional space $V$, the right side belongs to $(V)^3$. The order of vanishing of a product along a linear space is additive: use coordinates adapted to $V$ and take the least degree in those coordinates. Since $F$ has order at most one, $P F\in(V)^3$ would imply $P\in(V)^2$. This contradicts the classification and first-order-vanishing result.

In the remaining case, three factors lie in $U_h$ and the fourth is proportional to $F$ outside $U_h$. Every term on the right belongs to $(U_h)^2$. Since $F$ has order zero along $U_h$, this again forces $P\in(U_h)^2$, a contradiction.

## Proportional and constant factors

If two denominator factors are proportional, their common linear factor divides the cleared numerator. Since $P$ is irreducible of degree three, that factor must divide $F$. Cancelling it and combining the two rational terms gives an exact three-factor representation whose cleared numerator is a nonzero scalar multiple of $P$.

Such a representation is excluded by the already proved three-head tensor obstruction. There is also an elementary argument when its three factors are distinct: every pair must span one of the spaces $U_h$, forcing all three into the same $U_h$. Its cleared numerator would then lie in $(U_h)^2$, whereas $P$ does not. Further proportionalities would force a linear factor of $P$ and are impossible.

Nonzero constant denominators are covered by homogenization. Their factors are multiples of the homogenizing coordinate, which is independent of the six source coordinates. Zero denominator forms are excluded because an actual attention denominator is positive.

Thus there is no exact four-factor identity of the displayed kind with vanilla denominator orientations.

## Consequence and remaining gap

A four-head affine-fraction score agreeing with the source signs throughout the continuous cube would yield such an identity. Its cleared polynomial vanishes on an open smooth patch of the source zero set. The established irreducibility argument gives divisibility by $P$, and degree at most four leaves an affine multiplier $F$. The identity obstruction therefore rules out this continuous-cube representation.

This conclusion does not pass automatically to finite grids. Replica averaging preserves selected top mixed coefficients, rather than a full factorization of the averaged polynomial. In addition, a sequence of four-head representations can have denominator factors coalescing and numerator coefficients diverging. The normalized cleared-polynomial limit need not retain an exact four-factor representation. Handling both losses of structure, or finding a four- or five-head Boolean construction, remains necessary for improving the proved finite-family bounds of four through six.
