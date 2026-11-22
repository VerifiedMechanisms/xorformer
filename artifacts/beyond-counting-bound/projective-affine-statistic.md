# Projective Compilation and Punctured Parity

## Scope

This note proves an auxiliary upper construction in the unchanged attention model and an exponential obstruction to a proposed Helly argument. It does not prove the requested unboundedness of $n^2W(n)/2^n$.

## The projective compiler

### Theorem 1. Arbitrary affine statistics

Let $L(x)=c+\sum_{i=1}^n a_i x_i$ have arbitrary real coefficients. Let $P$ be a real univariate polynomial of degree at most $K$. If $f(x)$ is the positive-sign predicate of $P(L(x))$ on the Boolean cube, then $H^{\ast}(f)\leq K$.

**Proof.** First replace $P$ by $P-\varepsilon$ for sufficiently small $\varepsilon\gt0$. There are finitely many input values, so this preserves every positive sign and makes every nonpositive value strictly negative. The degree does not increase. Write $P$ for this shifted polynomial.

For $\delta\gt0$, put

$$ D_\delta(x)=1+\delta\sum_{i=1}^n x_i,\qquad t_\delta(x)=L(x)/D_\delta(x). $$

As $\delta\to0$, all values $P(t_\delta(x))$ converge to the nonzero values $P(L(x))$. Finiteness therefore supplies one positive $\delta$ preserving all their signs. Choose distinct real numbers $R_1,\ldots,R_K$ large enough that

$$ c+R_h\gt0,\qquad a_i+R_h\delta\gt0\quad\text{for all }h,i. $$

Each $L+R_hD_\delta$ is then an affine form with strictly positive constant and variable coefficients. Consequently $t_\delta(x)+R_h\gt0$ on the cube. Partial fractions give real $q,r_1,\ldots,r_K$ with

$$ \frac{P(t)}{\prod_{h=1}^K(t+R_h)}=q+\sum_{h=1}^K\frac{r_h}{t+R_h}. $$

This includes polynomials of smaller degree, and $K=0$ is the constant case. Substituting $t=t_\delta(x)$ gives

$$ S(x)=q+\sum_{h=1}^K\frac{r_hD_\delta(x)}{L(x)+R_hD_\delta(x)}. $$

The denominator of the partial-fraction quotient is positive, so $S(x)$ has the prescribed signs. Each numerator is affine and each denominator has strictly positive coefficients. The manuscript's exact positive-affine-ratio realization therefore implements each summand with one head; $q$ is absorbed into the threshold. This proves the claim. $\blacksquare$

### Corollary 2. Ordered sign changes

If a Boolean predicate factors through any affine statistic, and its labels change $C$ times along that statistic's increasing list of distinct cube values, then $H^{\ast}(f)\leq C$.

**Proof.** Place one simple polynomial root between each adjacent pair with different labels, and choose the overall sign at the final node. The resulting polynomial has degree $C$ and strict prescribed signs. Apply Theorem 1. $\blacksquare$

The affine coefficients may have mixed signs. No assertion is made that all degree $K$ multivariate polynomial threshold functions use $K$ heads.

## An exponential minimal infeasible sample

### Theorem 3. One flipped parity value

For $n\geq1$ and any vertex $v\in\lbrace0,1\rbrace^n$, define $f_v$ by flipping parity at $v$ alone. Then

$$ H^{\ast}(f_v)=n-1. $$

**Proof of the upper bound.** The distance

$$ d_v(x)=\sum_{i:v_i=0}x_i+\sum_{i:v_i=1}(1-x_i) $$

is affine and takes all values $0,1,\ldots,n$. Parity of $x$ is parity of $d_v(x)$, possibly complemented according to parity of $v$. Flipping the value at $d_v(x)=0$ makes the first two labels agree, while all subsequent adjacent pairs alternate. There are exactly $n-1$ sign changes. Corollary 2 applies.

Equivalently, an explicit sign polynomial is an appropriate signed multiple of

$$ \prod_{j=1}^{n-1}\big(t-j-\tfrac12\big). $$

For this polynomial one may use $\delta=1/(8n^2)$ in the compiler: for every cube input,

$$ 0\leq d_v(x)-\frac{d_v(x)}{1+\delta|x|}\leq\delta n^2=\tfrac18. $$

Thus the perturbation crosses none of the half-integer roots. Poles $R_h=8n^2(h+2)$, for $h=1,\ldots,n-1$, make every coefficient of $d_v+R_hD_\delta$ positive.

**Proof of the lower bound.** Fix any one coordinate to the bit opposite its value in $v$. The resulting face excludes $v$, and the restriction of $f_v$ is parity or complemented parity on $n-1$ free bits. Restriction cannot increase head complexity, output complementation preserves it, and parity on $n-1$ bits requires $n-1$ heads. The argument includes $n=1$, where the result is a constant. $\blacksquare$

### Corollary 4. Exponential Helly obstruction

Consider the family of parameter sets imposing the individual parity classification constraints at the $2^n$ cube vertices, with $n-1$ heads. Their full intersection is empty, but every proper subfamily has nonempty intersection.

**Proof.** The full parity table needs $n$ heads. For a proper subfamily, choose a missing vertex $v$ and use $f_v$. $\blacksquare$

Consequently these feasibility sets have Helly number at least $2^n$ for this head count. Their normalized real parameter count is only $2n(n-1)+1$. In particular, a universal infeasibility-certificate bound polynomial in the parameter count is false. This statement concerns certificates for infeasible samples, not sample compression for realizable labelings. It does not itself settle the exponentially large head regime of the main objective.

## Formal audit

The following files compile with warnings treated as errors:

- `formalization/HeadComplexity/Atoms/AffineStatisticPolynomial.lean` proves `HeadComplexity.computableWithHeadsN_affineStatisticPolynomial`, including the finite sign perturbation and exact positive-denominator construction.

- `formalization/HeadComplexity/Results/AffineStatisticProjective.lean` proves `HeadComplexity.computableWithHeadsN_of_univariateAffine`, `HeadComplexity.HStar_le_of_univariateAffine`, and `HeadComplexity.AffineStatisticProfile.HStar_le_alternations`.

- `formalization/HeadComplexity/Results/PuncturedParity.lean` proves `HeadComplexity.PuncturedParity.punctured_computable`, `proper_subset_parity_feasible`, and `full_parity_infeasible`. Thus the upper bound and the full minimal-infeasibility statement are formalized. The matching face-restriction lower bound in Theorem 3 is the written argument above.

All audited declarations use only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`. No model definition or pre-existing theorem statement was changed.
