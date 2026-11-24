# Quantitative repair for finitely many integral denominator directions

## Statement and status

This is a written positive repair theorem for a restricted denominator family. It allows arbitrary real numerators, arbitrary real poles, either coherent orientation, and arbitrary signed cancellation. It does not cover general target-dependent real directions and does not prove an unrestricted lower bound.

Let $n,G,B\geq1$ be integers. Fix $G$ vectors $w_g\in\lbrace1,\ldots,B\rbrace^n$ and write

$$ T_g(x)=\sum_{i=1}^n w_{g,i}x_i,\qquad L=nB,\qquad q=L+1,\qquad D=1+Gq(n+1). $$

Suppose a Boolean table $F:\lbrace0,1\rbrace^n\to\lbrace-1,+1\rbrace$ is represented by an original finite-head score whose every denominator is of the form $a_h+b_hT_{g(h)}(x)$ and is strictly positive on the whole cube. There is no bound on the original number of heads. A denominator with $b_h\lt0$ is allowed, as is the constant case subject to its original numerator admissibility restriction.

Then the same table has a representation by $Gq$ original admissible heads and one bias, with full-cube relative margin at least

$$ \Gamma(n,G,B)=\frac{1}{D!\bigl(1+G(n+1)q^2(2L+1)^{2L+1}\bigr)}. $$

All replacement denominators belong to the fixed list $h+T_g(x)$, for $1\leq g\leq G$ and $1\leq h\leq q$. In particular they have positive constant term and strictly positive slopes, so the genuine constructor `FracAtom.ofPositiveAffineRatio` applies. The construction changes poles and all numerator coefficients jointly.

## A finite integer feature space

Strictify the original finite classification table by a small change of its bias. Group together heads with the same $g$. On the level set $T_g(x)=k$, their sum is affine in $x$, because all denominators there are nonzero constants. Thus the strict score is a real linear combination of the following integer-valued features:

$$ 1,\qquad \psi_{g,k,0}(x)=\mathbf1[T_g(x)=k],\qquad \psi_{g,k,i}(x)=x_i\mathbf1[T_g(x)=k] \quad (1\leq i\leq n). $$

There are $D$ displayed features, each taking values in $\lbrace0,1\rbrace$. Empty levels cause no difficulty. The signed feature matrix has entries in $\lbrace-1,0,1\rbrace$.

Choose a maximal independent set of its columns, of cardinality $r\leq D$. Every original score vector is in the span of these columns. Consequently the selected $r$ columns admit a real strict separator on all rows. Their row vectors span $\mathbb R^r$: a vector orthogonal to every row would be a linear dependence of the selected columns. Scaling the separator makes all signed values at least one.

Apply the integer separator argument in [the one-head repair note](margin_repair_one_head_positive.md) to this full-rank integer matrix. Using the Leibniz determinant bound gives an integer coefficient vector with every coefficient bounded by $r!\leq D!$ and every signed evaluation at least one. Extend this vector by zeros in the unselected columns. Therefore there are integers $b,a_{g,k,i}$, each of absolute value at most $M=D!$, such that

$$ F(x)\left(b+\sum_{g=1}^G\sum_{i=0}^n a_{g,T_g(x),i}x_i\right)\geq1,\qquad x_0=1. $$

This step replaces the real cancellation pattern globally. It does not separately round the contribution from each original group.

The full-rank integer separator used here is kernel checked as `HeadComplexity.IntegerSeparatorMarginRepair.exists_bounded_integer_separator`. The selected-column reduction and the mixed-direction compiler in this note are written proofs.

## Fixed Cauchy interpolation

For a fixed pair $(g,i)$, interpolate the $q$ values $a_{g,k,i}$ at $k=0,\ldots,L$. Define

$$ Q(t)=\prod_{h=1}^q(t+h),\qquad P_{g,i}(t)=\sum_{k=0}^L a_{g,k,i}Q(k)\prod_{\substack{0\leq j\leq L\cr j\neq k}}\frac{t-j}{k-j}. $$

The polynomial $P_{g,i}$ has degree at most $L=q-1$ and satisfies $P_{g,i}(k)=a_{g,k,i}Q(k)$. Its partial fractions give

$$ \frac{P_{g,i}(t)}{Q(t)}=\sum_{h=1}^q\frac{c_{g,h,i}}{t+h},\qquad c_{g,h,i}=\frac{P_{g,i}(-h)}{\prod_{\ell\neq h}(\ell-h)}. $$

Every denominator factor here is a nonzero integer. For all relevant indices, $k+h\leq2L+1$ and $|-h-j|\leq2L+1$. Bounding each numerator factor individually yields

$$ |Q(k)|\leq(2L+1)^q,\qquad \left|\prod_{j\neq k}\frac{-h-j}{k-j}\right|\leq(2L+1)^L,\qquad |c_{g,h,i}|\leq qM(2L+1)^{2L+1}. $$

The exact interpolation identity is consequently

$$ \sum_{h=1}^q\frac{c_{g,h,i}}{k+h}=a_{g,k,i}\qquad(0\leq k\leq L). $$

## Admissibility and the full-cube norm

Choose the original admissible heads

$$ \phi_{g,h}(x)=\frac{c_{g,h,0}+\sum_{i=1}^n c_{g,h,i}x_i}{h+T_g(x)}. $$

Each denominator has positive constant term and every slope is at least one. Summing the interpolation identities shows that $b+\sum_{g,h}\phi_{g,h}$ equals the integer score from the previous section on the entire Boolean cube. Thus its smallest signed value is at least one.

Since all replacement denominators are at least one, their full-cube norms obey

$$ \|\phi_{g,h}\|_\infty\leq(n+1)qM(2L+1)^{2L+1}. $$

It follows that

$$ |b|+\sum_{g,h}\|\phi_{g,h}\|_\infty\leq M\bigl(1+G(n+1)q^2(2L+1)^{2L+1}\bigr). $$

Dividing the signed-value bound by this full-cube amplitude proves the stated margin. No rescaling argument is being used to improve the ratio.

## What scale this reaches

For fixed $b_0\geq0$, suppose $B\leq n^{b_0}$ and $G\leq\exp(t/2)$, where either $t=\sqrt n$ or $t=n/\log n$. Then

$$ \log\frac{1}{\Gamma}\leq D\log D+\log\bigl(1+G(n+1)q^2(2L+1)^{2L+1}\bigr)=\exp(t/2)n^{O_{b_0}(1)}\leq\exp(t) $$

for every sufficiently large $n$. The final inequality follows because $t/\log n\to\infty$ in both cases. Hence the repaired margin is at least $\exp(-\exp(t))$. Its width $Gq\leq\exp(t/2)n^{b_0+1}+\exp(t/2)$ is smaller than either critical width $c2^n/n^{3/2}$ or $c2^n\log n/n^2$ for every fixed $c\gt0$ and all sufficiently large $n$.

Thus the intermediate high-margin count applies to this restricted class, including all targets that have arbitrarily many poles along a sufficiently small collection of bounded integral directions. No assumption on the original coefficient height is needed.

## The first failed exponential-width inequality

The compiler's width is $G(L+1)$ rather than a constant times the original width automatically. If the original heads are mostly in different directions, even assuming bounded integral weights costs a factor of order $L$. There is no proof that nearby directions can be merged while preserving the truth table.

Even in the favorable regime $G(L+1)\asymp H$, the displayed determinant guarantee has $D\asymp nH$. At $H\asymp2^n/n^{3/2}$, the exponent in that guarantee is

$$ D\log D\asymp n^2H\asymp2^n\sqrt n, $$

whereas the required bound is at most $\exp(\sqrt n)$. At $H\asymp2^n\log n/n^2$, it is of order $2^n\log n$, whereas the required bound is at most $\exp(n/\log n)$. Both comparisons fail exponentially. These are failures of the proved determinant guarantee, not counterexamples to a better repair.

A new ingredient would have to exploit the joint Boolean structure to avoid a determinant bound exponential in the total feature dimension, or else compile into a much smaller integer feature family at essentially the original width. The same first obstruction persists after passing from one common direction to a small collection of integral directions.
