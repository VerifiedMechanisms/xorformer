# Margin repair cannot retain an arbitrary denominator family

## Scope

The desired repair may change every denominator and may increase width by a fixed factor. No obstruction to that fully quantified repair is proved here.

This note rules out a narrower repair which retains a prescribed denominator family while changing every numerator and the bias. The obstruction concerns *every* such refitted representation of one truth table. It is stronger than displaying one poorly conditioned score. The truth table may still have a well conditioned representation using other admissible heads.

The finite pencil construction below is a written proof. The separate denominator oscillation theorem is kernel checked in `formalization/HeadComplexity/Research/NearConstantMarginObstruction.lean`.

## A finite fixed-family theorem

Let $n\geq1$, $N=2^n$, and choose integers $H,r$ satisfying

$$ 1+n(r+1)\lt H\leq N. $$

Choose distinct positive numbers $\lambda_1,\ldots,\lambda_H$ and define

$$ C(x)=1+\sum_{i=1}^n2^{i-1}x_i,\qquad B_{h,t}(x)=1+t\lambda_h C(x). $$

The values of $C$ on the cube are the distinct integers $1,\ldots,N$. For every $t\gt0$, the denominators have positive constant coefficients and strictly positive slopes, so arbitrary affine numerators over them are admissible original-model heads.

**Theorem 1.** There is one strict Boolean truth table $F$ with the following two properties.

1. For every $t\gt0$, $F$ is represented by $H$ original heads with the displayed denominators and constant numerators.

2. Fix any $t\gt0$ and any affine numerators $A_h$, arbitrary real bias $b$, and strict representation $S=b+\sum_hA_h/B_{h,t}$ of this same $F$. Its full-cube relative head margin satisfies

$$ \frac{\min_xF(x)S(x)}{|b|+\sum_h\|A_h/B_{h,t}\|_\infty}\leq\left(tN\max_h\lambda_h\right)^{r+1}. $$

The table $F$ is independent of $t$. Adding copies of denominators already in the displayed family does not change the conclusion, because their numerators can be combined, and the combined head norm is no larger than the sum of the original norms. Arbitrarily many copies therefore do not repair the margin.

### Proof. A missing sign vector

Let

$$ U_r=\mathrm{span}\left(\lbrace1\rbrace\cup\lbrace x_iC(x)^j:1\leq i\leq n,\ 0\leq j\leq r\rbrace\right). $$

Its dimension is at most $1+n(r+1)$. Every table $L(x)C(x)^j$ with affine $L$ and $0\leq j\leq r$ belongs to $U_r$. Indeed, multiplying the identity $C=1+\sum_i2^{i-1}x_i$ by $C^{j-1}$ expresses the constant-numerator term $C^j$ using $C^{j-1}$ and $x_iC^{j-1}$. Induction starts from $1$.

Select any $H$ cube vertices. Since the restrictions of $U_r$ to these vertices form a proper linear subspace of $\mathbb R^H$, choose a nonzero vector $w$ orthogonal to that subspace. Label the selected vertex $i$ by the sign of $w_i$ when $w_i\neq0$, and by either sign when $w_i=0$. No member of $U_r$ strictly realizes these labels. Otherwise each product $w_i u_i$ would be nonnegative, at least one would be positive, and their sum could not be zero.

Interpolate the prescribed values $\pm1$ at the $H$ distinct selected values of $C$ by a polynomial $p$ of degree at most $H-1$. Add a constant $\delta$ with $|\delta|\lt1/2$ that avoids the finitely many numbers $-p(k)$ for $1\leq k\leq N$. The selected signs remain unchanged, while $p+\delta$ is nonzero at every cube value. Replace $p$ by $p+\delta$ and define $F(x)=\mathrm{sign}(p(C(x)))$. Thus $F$ is strict on the full cube and has no strict representative in $U_r$.

### Proof. Every scale realizes the table

For every $t\gt0$, ordinary partial fractions give constants $a_h(t)$ satisfying

$$ \frac{p(z)}{\prod_{h=1}^H(1+t\lambda_hz)}=\sum_{h=1}^H\frac{a_h(t)}{1+t\lambda_hz}. $$

For completeness, the polynomials $\prod_{g\neq h}(1+t\lambda_gz)$ are a basis of the real polynomials of degree at most $H-1$. Evaluating a linear relation at $z=-1/(t\lambda_h)$ isolates the coefficient indexed by $h$, multiplied by a nonzero number because the $\lambda_h$ are distinct. There are $H$ independent polynomials in an $H$-dimensional space. This proves the displayed identity without a condition-number assumption.

The common denominator is positive for $z=C(x)\gt0$. Hence this score strictly realizes $F$ for every positive $t$. Constant numerators and the displayed strictly coherent denominators are admissible.

### Proof. Every refitted representation has small margin

Write $\varepsilon=tN\max_h\lambda_h$. Replace every head in any refitted representation by

$$ Q_h(x)=A_h(x)\sum_{j=0}^{r}(-t\lambda_hC(x))^j. $$

The finite geometric identity gives

$$ \frac{A_h(x)}{B_{h,t}(x)}-Q_h(x)=\frac{A_h(x)}{B_{h,t}(x)}(-t\lambda_hC(x))^{r+1}. $$

Therefore the summed approximation $Q=b+\sum_hQ_h$ belongs to $U_r$ and satisfies

$$ |S(x)-Q(x)|\leq\varepsilon^{r+1}\sum_h\|A_h/B_{h,t}\|_\infty\leq\varepsilon^{r+1}\left(|b|+\sum_h\|A_h/B_{h,t}\|_\infty\right). $$

If the relative margin were greater than $\varepsilon^{r+1}$, this approximation would preserve every strict label, contradicting the construction of $F$. This proves Theorem 1. $\blacksquare$

## Exponential order at the disputed widths

Suppose $H\geq4n$ and set $r=\lfloor H/(2n)\rfloor-1$. Then $1+n(r+1)\leq1+H/2\lt H$, while $r+1\geq H/(4n)$. Choose

$$ t=\frac1{2N\max_h\lambda_h}. $$

Every displayed denominator then lies between $1$ and $3/2$ on the full cube. Theorem 1 supplies an $H$-head truth table for which *every* representation using those denominators, even with repeated copies and arbitrary affine numerator refitting, has relative margin at most

$$ 2^{-(r+1)}\leq\exp\left(-\frac{H\log2}{4n}\right). $$

At $H=\lfloor cN/n^{3/2}\rfloor$ with any fixed $c\gt0$, the quantity $H/n$ grows faster than $\exp(\sqrt n)$. The resulting bound is eventually smaller than $\exp(-\exp(\sqrt n))$. At $H=\lfloor cN\log n/n^2\rfloor$, it is eventually smaller than $\exp(-\exp(n/\log n))$, because

$$ \log(H/n)=n\log2-O(\log n),\qquad n/\log n=o(n). $$

These comparisons rule out a denominator-retaining version of either requested repair. The same selected truth table can have a better representation using other denominators. The theorem does not quantify over those alternatives and consequently does not refute the requested full repair.

## A kernel-checked denominator oscillation obstruction

The Lean module proves the following more general approximation implication. Let the heads be genuine `FracAtom` values, with arbitrary signed output coefficients absorbed into their numerators. Suppose positive numbers $q_h$ satisfy, on the full Boolean cube,

$$ \left|1-\frac{B_h(x)}{q_h}\right|\leq\varepsilon,\qquad \varepsilon\geq0. $$

If a strict representation has relative margin $\gamma\gt\varepsilon^{d+1}$, its target has threshold degree at most $d+1$. The geometric approximant has degree at most $d+1$, and the previous relative-error argument preserves every sign. There is no bound on the number of heads, numerator coefficients, or cancellation.

Taking the target to be full parity and using its already formalized threshold degree $n$ gives, for $n\geq2$,

$$ \gamma\leq\varepsilon^{n-1}. $$

The exact declarations are `HeadComplexity.NearConstantMarginObstruction.thresholdDegLE_of_near_constant_margin`, `margin_le_of_threshold_degree_gap`, and `parity_margin_le_of_near_constant`. Their inputs include explicit amplitude upper bounds and the signed margin inequality. Taking each amplitude to equal its full-cube supremum gives the stated relative margin. Their transitive axiom output is `[propext, Classical.choice, Quot.sound]`.

The finite pencil theorem uses the more refined space $U_r$ instead of total degree. Its dimension obstruction and partial-fraction existence are written proofs and are not claimed to be formalized by the parity theorem.

## First surviving repair lemma

A useful next statement must allow new denominators. In a sufficient version, every table represented by at most $H$ original heads has some representation by at most $C H$ original heads whose relative margin is at least the requested threshold. A weaker count could bound tables for which every such new representation has smaller margin.

Theorem 1 establishes neither conclusion. It shows why compactness of denominator charts, bounded denominator ranges, refitting numerators, and repeating a fixed dictionary do not settle that first surviving lemma.
