# Boolean Differences and Their Positive Weight Kernel

## Exact identity

Let $r\geq1$, $D\gt0$, and $b_i\gt0$. The numerator coefficients $A,a_i$ are arbitrary real numbers. Define the alternating Boolean difference

$$ \mathcal D(A,D;a,b)=\sum_{S\subseteq\lbrace1,\ldots,r\rbrace}(-1)^{|S|}\frac{A+\sum_{i\in S}a_i}{D+\sum_{i\in S}b_i}. $$

There are strictly positive weights $w_i(D)$, summing to one, for which

$$ \mathcal D(A,D;a,b)=K(D)\left(A-D\sum_{i=1}^r w_i(D)\frac{a_i}{b_i}\right),\qquad K(D)\gt0. $$

These weights depend on the base denominator $D$. Replacing them by constant weights is generally invalid.

**Proof.** Write

$$ G(t)=\prod_{i=1}^r(1-e^{-b_i t}),\qquad K(D)=\int_0^\infty e^{-Dt}G(t)dt,\qquad J_i(D)=\int_0^\infty e^{-(D+b_i)t}\prod_{j\neq i}(1-e^{-b_jt})dt. $$

Expanding the finite product and using the elementary Laplace integral for a positive reciprocal gives

$$ \mathcal D=AK(D)-\sum_i a_iJ_i(D). $$

All these integrals converge, and $K,J_i$ are strictly positive. The product rule and integration by parts give

$$ \sum_i b_iJ_i(D)=\int_0^\infty e^{-Dt}G'(t)dt=DK(D). $$

Both boundary terms vanish: $G(0)=0$, while $G(t)\leq1$ and $D\gt0$. Set $w_i=b_iJ_i/(DK)$. This proves the identity and every positivity assertion. $\blacksquare$

The formula applies to a face of an actual positive-slope head, with $A$ and $D$ evaluated on the remaining input coordinates. All coefficients of the numerator remain unrestricted. For negative-slope heads, complementing the differentiated coordinates gives the corresponding identity with the appropriate alternating sign.

## A precise ordering invariant

Put $c_b(t)=b/(e^{bt}-1)$. Then

$$ F_i(D):=b_iJ_i(D)=\int_0^\infty e^{-Dt}G(t)c_{b_i}(t)dt,\qquad w_i(D)=\frac{F_i(D)}{DK(D)}. $$

If $b_i\lt b_j$, then $w_i(D)\gt w_j(D)$ for every $D\gt0$. Moreover, if $D_1\lt D_2$, then

$$ w_i(D_1)w_j(D_2)-w_i(D_2)w_j(D_1)\gt0. $$

**Proof.** The function $b\mapsto b/(e^{bt}-1)$ is strictly decreasing for $t\gt0$: the numerator of its derivative has the sign of $e^z(1-z)-1$, which is negative for $z\gt0$. This proves the first assertion by integration.

For the second assertion, the ratio $R(t)=c_{b_i}(t)/c_{b_j}(t)$ is strictly increasing. Indeed,

$$ \frac{d}{dt}\log R(t)=\frac{b_j}{1-e^{-b_jt}}-\frac{b_i}{1-e^{-b_it}}\gt0, $$

since $z/(1-e^{-z})$ is strictly increasing on the positive half-line; its derivative numerator is $1-e^{-z}(1+z)\gt0$.

Expand $F_i(D_1)F_j(D_2)-F_i(D_2)F_j(D_1)$ as a double integral and pair the regions $s\gt t$ and $s\lt t$. The integrand on $s\gt t$ becomes

$$ G(s)G(t)c_{b_j}(s)c_{b_j}(t)(R(s)-R(t))\left(e^{-D_1s-D_2t}-e^{-D_2s-D_1t}\right). $$

Every factor is positive. The integrals are absolutely convergent by the estimates already used above, so this pairing is valid. Division by the positive column normalizers $D_jK(D_j)$ proves the displayed inequality. $\blacksquare$

Thus the ordered weight kernel has positive minors of order two. This fact alone does not establish total positivity at higher orders, an oscillation bound for arbitrary signed combinations, or an unrestricted head lower bound.

## Failure of affine sign transfer

Consider the single head

$$ R(x,y,u,v)=\frac{127/210+(8/15)(x+y)+u}{1+x+y+u+2v}. $$

Its denominator constant and all four slopes are strictly positive, so the manuscript's exact one-head realization theorem applies. Define

$$ T(x,y)=R(x,y,0,0)-R(x,y,1,0)-R(x,y,0,1)+R(x,y,1,1). $$

Direct rational arithmetic gives

$$ T(0,0)=1/504,\qquad T(0,1)=T(1,0)=-1/1800,\qquad T(1,1)=1/4200. $$

Consequently $T$ has the signs of equality on two bits and has no affine sign representation. To see this even with the manuscript's non-strict false-label convention, suppose $c$, $c+a+b$ are positive while $c+a$, $c+b$ are nonpositive. Adding the latter inequalities contradicts the sum of the former two.

The underlying algebraic identity, with nonzero denominators, is

$$ \frac A D-\frac{A+a}{D+u}-\frac{A+b}{D+v}+\frac{A+a+b}{D+u+v}=\frac{Auv(2D+u+v)-avD(D+v)-buD(D+u)}{D(D+u)(D+v)(D+u+v)}. $$

For comparison, the continuous mixed derivative of an affine ratio has an affine expression controlling its sign:

$$ \partial_S(A/B)=(-1)^{|S|}|S|!\frac{\prod_{i\in S}b_i}{B^{|S|+1}}\left(A-\frac B{|S|}\sum_{i\in S}\frac{a_i}{b_i}\right). $$

This follows by differentiating $B^{-1}$ and using the product rule; at most one derivative can land on the affine numerator. The explicit Boolean counterexample proves that the affine sign conclusion cannot be transferred through integration over a face.

## Audit and consequence for the research

`formalization/HeadComplexity/Atoms/BooleanDifferenceBarrier.lean` checks `second_difference_identity`, `difference_values`, `difference_signs`, `no_affine_sign_representation`, and `exists_actual_atom`. The last theorem supplies an actual `FracAtom 4`, with equality of its values to the displayed ratio at every cube vertex. The build passes, and all five declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

The general integral formula and the two-by-two determinant theorem above are complete written proofs, not claims of Lean formalization. The model is unchanged. The proposed transfer from affine signs of continuous derivatives to affine signs of Boolean differences is refuted and blocked. Any use of the positive weight kernel for the main lower bound still needs a new argument controlling arbitrary signed sums and all target-dependent denominators.
