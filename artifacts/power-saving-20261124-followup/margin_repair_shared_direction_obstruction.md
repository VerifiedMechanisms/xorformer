# Changing poles along one direction still does not repair sparse margins

## Scope and status

This is a written theorem about the original admissible head class, under one explicit restriction: every nonconstant denominator has slopes proportional to one fixed binary address direction, with either common sign. The numerator is arbitrary affine, every pole and scale may change with the target, and the head count is unrestricted in the margin obstruction.

The result strengthens the [fixed-pencil obstruction](margin_repair_fixed_pencil_obstruction.md). Repeating the old denominators is unnecessary: every new admissible pole along the same direction is covered. Changing denominator *directions* remains outside the theorem. No unrestricted lower bound on `HeadComplexity.worstCaseHeadComplexity` follows.

## The shared direction

Let $n\geq1$, $N=2^n$, and put

$$ z(x)=\sum_{i=1}^n2^{i-1}x_i. $$

The cube values of $z$ are exactly $0,\ldots,N-1$. Allow every denominator of either form

$$ B(x)=a+bz(x),\qquad B(x)=a+b(N-1-z(x)),\qquad a\gt0,\quad b\geq0. $$

When $b\gt0$, all slopes are strictly positive in the first form and strictly negative in the second, so arbitrary affine numerators are admissible in the original model. Including arbitrary affine numerators when $b=0$ enlarges the original family and only strengthens the obstruction. This family is exactly the collection of positive cube denominators whose nonzero slope vector is a scalar multiple of the displayed binary vector, together with the constant denominators.

## One comparison space approximates every pole

For $0\leq k\lt n$, define the positive and reflected dyadic shells

$$ E_k^+=\lbrace x:2^k\leq z(x)\lt2^{k+1}\rbrace,\qquad E_k^-=\lbrace x:2^k\leq N-1-z(x)\lt2^{k+1}\rbrace. $$

Let $U_r$ be the span of the two endpoint indicators, together with all tables

$$ \boldsymbol1_{E_k^\sigma}(x)L(x)z(x)^j,\qquad \sigma\in\lbrace+,-\rbrace,\quad 0\leq k\lt n,\quad 0\leq j\leq r, $$

where $L$ ranges over affine functions. Since there are $2n$ shells and at most $(n+1)(r+1)$ displayed coefficients on each shell,

$$ \dim U_r\leq2+2n(n+1)(r+1)\leq2(n+1)^2(r+1). $$

The free constant table belongs to this space: the positive shells and the zero endpoint partition the cube. All comparisons are on the entire cube.

**Lemma 1.** For every allowed denominator $B$ and every affine numerator $A$, there is a table $Q\in U_r$ satisfying

$$ \left|\frac{A(x)}{B(x)}-Q(x)\right|\leq2^{-(r+1)}\left|\frac{A(x)}{B(x)}\right| $$

at every input. In particular, the uniform error is at most $2^{-(r+1)}\|A/B\|_\infty$.

**Proof.** First take $B=a+bz$. On the shell $E_k^+$, put $q_k=a+b2^k$. Then

$$ q_k\leq B(x)\leq2q_k,\qquad0\leq1-\frac{B(x)}{2q_k}\leq\frac12. $$

On this shell use the table

$$ Q(x)=\frac{A(x)}{2q_k}\sum_{j=0}^{r}\left(1-\frac{B(x)}{2q_k}\right)^j. $$

It is affine times a polynomial in $z$ of degree at most $r$, multiplied by the shell indicator. At the remaining endpoint $z=0$, use the exact value $A(x)/a$, supported on that one vertex. The resulting table belongs to $U_r$.

The geometric identity makes its error exactly

$$ \frac{A(x)}{B(x)}\left(1-\frac{B(x)}{2q_k}\right)^{r+1} $$

on a shell, and zero at the endpoint. This proves the estimate for the positive orientation. For $B=a+b(N-1-z)$, use the reflected shells and the other endpoint. A polynomial in $N-1-z$ of degree at most $r$ is also a polynomial in $z$ of degree at most $r$, so the same fixed space works. The case $b=0$ obeys the same proof. $\blacksquare$

## A truth table which every shared-direction representation represents with small margin

**Theorem 2.** If

$$ 2(n+1)^2(r+1)\lt H\leq N, $$

there is a strict truth table $F$ with these properties:

1. It has an original-model representation with $H$ heads, all having strictly positive slopes proportional to the binary direction.

2. Every representation of $F$ whose denominators belong to the allowed shared-direction family, with any finite head count, arbitrary affine numerators, arbitrary real bias, and arbitrary signed cancellation, has relative head-amplitude margin at most $2^{-(r+1)}$.

**Proof.** Select $H$ vertices. Their restrictions of $U_r$ lie in a proper subspace of $\mathbb R^H$. A nonzero orthogonal vector supplies a strict sign pattern omitted by that subspace, as in the fixed-pencil theorem. Interpolate the corresponding values $\pm1$ by a univariate polynomial $p$ of degree at most $H-1$ at the selected distinct values of $z$. A constant perturbation of absolute value less than $1/2$ preserves those signs and avoids zeros at all $N$ cube values. Let $F=\mathrm{sign}(p(z))$.

The table $F$ has no strict representative in $U_r$. On the other hand, partial fractions express

$$ \frac{p(z)}{\prod_{h=1}^H(z+h)}=\sum_{h=1}^H\frac{a_h}{z+h}. $$

Every denominator is positive on the cube with strictly positive binary slopes. The product denominator is positive, so these $H$ genuine original heads strictly represent $F$.

Now consider any shared-direction representation $S=b+\sum_h\phi_h$ of this $F$, allowing new poles, either orientation, and any finite width. Apply Lemma 1 separately to every head and retain the bias exactly. The sum $Q$ lies in $U_r$ and obeys

$$ |S(x)-Q(x)|\leq2^{-(r+1)}\sum_h\|\phi_h\|_\infty\leq2^{-(r+1)}\left(|b|+\sum_h\|\phi_h\|_\infty\right). $$

A larger relative margin would make $Q$ strictly represent $F$, a contradiction. This proves the quantifier over every such representation, including all new same-direction denominators and arbitrary head overhead. $\blacksquare$

## Quantitative comparison with the research targets

For $H\geq8(n+1)^2$, choose

$$ r+1=\left\lfloor\frac{H}{4(n+1)^2}\right\rfloor. $$

Then the dimension inequality holds, and $r+1\geq H/[8(n+1)^2]$. Theorem 2 supplies an $H$-head original truth table for which every shared-direction representation has relative margin at most

$$ \exp\left(-\frac{H\log2}{8(n+1)^2}\right). $$

At $H=\lfloor cN/n^{3/2}\rfloor$, this is eventually below $\exp(-\exp(\sqrt n))$. At $H=\lfloor cN\log n/n^2\rfloor$, it is eventually below $\exp(-\exp(n/\log n))$. In both cases, the logarithm of $H/(n+1)^2$ is $n\log2-O(\log n)$, which dominates the desired inner exponent.

Therefore a theorem repairing arbitrary narrow representations cannot retain their one-dimensional slope span, even if it may choose completely new poles and arbitrarily many heads. The construction does not exclude a repair which introduces genuinely different denominator directions. No statement here asserts that the displayed truth table is hard for that larger class.

## Verification boundary

The proof uses finite-dimensional linear algebra, polynomial interpolation, partial fractions, and the exact geometric identity. These arguments are written proofs. The original-model reciprocal admissibility bridge is formalized in `HeadComplexity.Atoms.PositiveAffineRatio`; the geometric identity and scalar relative-error estimate are formalized in `HeadComplexity.Research.ConditionedReciprocalApproximation`. This note does not claim that its shell construction, dimension argument, or existential truth table has been kernel checked.

The root agent independently read the full proof and checked the full-cube shell partition, dimension estimate, missing-label argument, constant perturbation, inclusion of the bias, positive admissible partial fractions, unrestricted finite width within the shared-direction family, both orientations, and the two target-scale comparisons.
