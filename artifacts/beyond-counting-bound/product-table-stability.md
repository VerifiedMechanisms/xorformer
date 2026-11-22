# Positive denominator products need not have stable value tables

## Statement

This is an obstruction to a proposed invariant, not a lower bound on head complexity. It concerns the generating polynomial of the Boolean value table. It does not concern the ordinary product of affine polynomials, which is stable in this example.

Let the four rows of $b$ be $(10,10,1,1)$, $(1,1,10,10)$, $(10,1,10,1)$, and $(1,10,1,10)$. For $x \in \lbrace 0,1\rbrace^4$, define

$$ D_h(x)=1+\sum_{i=0}^3 b_{hi}x_i,\qquad Q(x)=\prod_{h=0}^3 D_h(x),\qquad F(z)=\sum_{x\in\lbrace 0,1\rbrace^4}Q(x)\prod_{i=0}^3 z_i^{x_i}. $$

Every denominator has strictly positive coefficients and is admissible in the manuscript's model. Each individual value-table generating polynomial is real stable. Nevertheless, $F$ has a zero with every coordinate in the open upper half-plane. A positive external field applied to its coefficients also gives a probability measure with a strictly positive pairwise covariance.

Here real stability means that a real polynomial is nonzero whenever every input coordinate has strictly positive imaginary part. The connection between stability and negative dependence is developed in [Borcea, Brändén, and Liggett, *Negative dependence and the geometry of polynomials*](https://arxiv.org/abs/0707.2340). The counterexample below is verified directly and does not rely on a closure theorem from that paper.

## Proof

### Individual factors

For any $D(x)=b_0+\sum_i b_i x_i$ with all coefficients strictly positive, its value-table generating polynomial satisfies

$$ F_D(z)=\prod_i(1+z_i)\left(b_0+\sum_i\frac{b_i z_i}{1+z_i}\right). $$

When every $\mathrm{Im}(z_i)\gt 0$, all factors $1+z_i$ are nonzero, and

$$ \mathrm{Im}\left(\frac{z_i}{1+z_i}\right)=\frac{\mathrm{Im}(z_i)}{|1+z_i|^2}\gt 0. $$

Thus the expression in parentheses has positive imaginary part and cannot vanish. In particular, all four individual generators are stable. Multiplying the denominator values corresponds to taking the coefficientwise product of these generators, not their ordinary polynomial product.

### Exact product table

The values $Q(x)$, indexed by $v=\sum_i2^i x_i$ from $0$ through $15$, are

$$ (1,484,484,9072,484,9072,20736,81796,484,20736,9072,81796,9072,81796,81796,279841). $$

Consequently,

$$ F(z)=1+484\sum_i z_i+9072(z_0z_1+z_0z_2+z_1z_3+z_2z_3)+20736(z_0z_3+z_1z_2)+81796\sum_{i\lt j\lt k}z_i z_j z_k+279841z_0z_1z_2z_3. $$

In particular,

$$ F(z,t,t,w)=a(t)+b(t)(z+w)+d(t)zw,\qquad a(t)=1+968t+20736t^2,\qquad b(t)=484+18144t+81796t^2,\qquad d(t)=20736+163592t+279841t^2. $$

Set

$$ t=\frac1{10}+\frac{\mathrm{i}}{10000},\qquad w=-\frac{1252875804328031226236292}{16013505298103043438130897}+\frac{23924656286642536357360}{16013505298103043438130897}\mathrm{i}. $$

Direct rational arithmetic gives

$$ w=-\frac{a(t)+b(t)\mathrm{i}}{b(t)+d(t)\mathrm{i}},\qquad F(\mathrm{i},t,t,w)=0. $$

All four imaginary parts are strictly positive. This proves failure of real stability without invoking a characterization by derivatives.

### Positive covariance

At $z=(1/10,1/10,1/10,1/10)$, direct differentiation gives

$$ F(z)=\frac{13273681}{10000},\qquad \partial_0F(z)=\partial_3F(z)=\frac{7105721}{1000},\qquad \partial_0\partial_3F(z)=\frac{3989361}{100}. $$

The corresponding Rayleigh difference is strictly negative:

$$ \partial_0F(z)\partial_3F(z)-F(z)\partial_0\partial_3F(z)=-\frac{1231117189}{500}. $$

Define the probability of $x$ to be proportional to $Q(x)10^{-|x|}$. Its normalizing constant is $Z=F(1/10,1/10,1/10,1/10)$. Then

$$ \mathrm{Cov}(x_0,x_3)=\frac{2462234378000}{176190607289761}\gt 0. $$

This follows either from the displayed derivatives or by summing the sixteen rational weights. $\blacksquare$

## Audit and consequence

`formalization/HeadComplexity/Atoms/ProductTableStability.lean` verifies the positive denominator coefficients, every table entry, the expansion of the generating polynomial, the explicit upper-half-plane zero, and positive covariance. The central declarations are `HeadComplexity.ProductTableStability.exists_upper_half_plane_zero` and `HeadComplexity.ProductTableStability.covariance_positive`. They use Lean's standard axioms only. The general proof of stability for an individual affine denominator generator is the elementary written argument above.

`verify_product_table_stability.py` independently checks the data, complex zero, and exact covariance using rational arithmetic. No approximate eigenvalue or root computation is used.

This rejects the proposed invariant that products of admissible positive affine denominators always have stable Boolean value-table generators, even though each factor does. It also rejects a universal negative-association claim for the associated externally weighted measures. It does not exclude weaker invariants, establish a sign-pattern count, or prove the run's target. The definition of $W(n)$ and the manuscript architecture are unchanged.
