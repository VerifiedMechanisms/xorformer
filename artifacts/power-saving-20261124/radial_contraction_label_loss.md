# Finite radial contraction can lose all representations of a label table

## Statement

Let $X=\lbrace 0,1\rbrace^4$, and number each vertex by $v=x_0+2x_1+4x_2+8x_3$. Define a Boolean target $f$ whose positive vertices are $3,5,12,13,15$. Put

$$ C_1=6x_0+7x_1+2x_2+5x_3,\qquad C_2=2x_0+2x_1+x_2+x_3,\qquad D_j(t)=1+tC_j. $$

The target has an original-model representation with two heads using $D_1(1),D_2(1)$. However, for every $0\lt t\leq 1/10$, no score

$$ c+\frac{A_1(x)}{D_1(t,x)}+\frac{A_2(x)}{D_2(t,x)} $$

represents $f$, even when the bias and both affine numerators are chosen arbitrarily and depend on $t$. This includes the convention that true labels require a positive score and false labels allow a zero score.

Every displayed denominator is strictly positive on the entire cube and has strictly positive slopes for $t\gt 0$. This is a failure of one proposed reduction to collisions, not a lower bound on unrestricted head complexity. A path changing the denominator directions is not covered.

## Exact two-head witness

At $t=1$, use

$$ S(x)=-15+\frac{-1008x_1+1350x_3}{D_1(1,x)}+\frac{42x_0+398x_1+22x_2-464x_3}{D_2(1,x)}. $$

The cleared values $D_1D_2S$, in increasing vertex order, are

$$ (-15,-21,-200,70,-24,36,-432,-96,-264,-384,-270,-114,154,100,-75,147). $$

All values are nonzero, and the positive entries are exactly the target vertices. Positivity of both denominators proves the representation. The positive affine-ratio constructor in the repository supplies the bridge to the original shared-attention head model.

## Certificate excluding every small scale

Write $F(v)=1$ at the positive vertices and $F(v)=-1$ elsewhere. Use the ordered support

$$ (v_0,\ldots,v_8)=(1,2,3,5,7,9,11,12,15). $$

Define the nine weights as follows.

$$ \begin{aligned} w_0&=-130t^3+343t^2+215t+48,\cr w_1&=-(2t+5)(5t-1)(7t+4),\cr w_2&=-12(t-2)(10t^2+11t+7),\cr w_3&=-50t^3+157t^2+269t+44,\cr w_4&=-46t^3+139t^2+239t+144,\cr w_5&=-10t^3-199t^2+25t+16,\cr w_6&=-10t^3+169t^2+65t+84,\cr w_7&=w_1,\cr w_8&=5(2t^3+23t^2+19t+16). \end{aligned} $$

All nine weights are strictly positive when $0\lt t\leq 1/10$. For example, $t^2\leq 1/100$ and $t^3\leq 1/1000$ give $w_5\geq 16-10/1000-199/100\gt 0$. The other expanded expressions have a single negative cubic term dominated by their positive constant; the two factored expressions have visibly positive signs in this interval.

For arbitrary affine $A_1,A_2$ and arbitrary $c$, put

$$ P(x)=cD_1(t,x)D_2(t,x)+A_1(x)D_2(t,x)+A_2(x)D_1(t,x). $$

The exact polynomial identity is

$$ \sum_{i=0}^8 w_i(t)F(v_i)P(v_i)=0. $$

One can check the identity by collecting the eleven independent coefficients of $c,A_1,A_2$. The supplied symbolic script checks each coefficient over the rational polynomial ring; the Lean proof independently checks the expanded identity using the ring tactic.

If the score represented $f$, each summand would be nonnegative: at negative vertices $P\leq 0$, and at positive vertices $P\gt 0$. At vertex $v_2=3$ the summand would be strictly positive. The sum would therefore be positive, contradicting the identity. This proves the asserted impossibility for every small scale and every choice of numerators.

## Verification and scope

The initial floating-point linear program in `probe_radial_contraction.py` was used only to discover a candidate. It is not the proof. `exact_radial_contraction.py` recovers an exact rational witness and the symbolic annihilating weights. The complete general statement above is separately kernel checked in `formalization/HeadComplexity/Research/RadialContraction.lean`.

The declarations are `HeadComplexity.RadialContraction.target_computableWith_two_heads` and `HeadComplexity.RadialContraction.not_small_scale_represents_target`. Both report only `propext`, `Classical.choice`, and `Quot.sound`. There is no new axiom and no `sorry`. The first uses the existing original-model bridge, and the second quantifies over all real affine numerator coefficients and the bias.

No representation with other denominator directions is excluded. No asymptotic bound for the original worst-case head complexity follows from this example.
