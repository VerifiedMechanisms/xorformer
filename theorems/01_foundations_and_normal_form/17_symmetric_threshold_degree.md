# Theorem 1.17. Symmetric threshold degree

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and let $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ be a [symmetric function (Definition 1.17)](../../definitions/17_symmetric_functions.md), with $f(x)=F(|x|)$. Its [threshold degree (Definition 1.14)](../../definitions/14_threshold_degree.md) $\deg _{\pm}(f)$ equals its [sign-change count (Definition 1.18)](../../definitions/18_sign_change_count.md) $C(F)$:

$$ \deg_{\pm}(f)=C(F). $$

There is a univariate polynomial $P\in\mathbb{R}[z]$ of degree $C(F)$ such that $x\mapsto P(|x|)$ is a [strict sign representation (Definition 1.13)](../../definitions/13_strict_sign_representation.md) of $f$.

## Proof

**Upper bound and witness.** Set $C=C(F)$ and let

$$ J=\lbrace j\in\lbrace1,\ldots,n\rbrace:F(j-1)\neq F(j)\rbrace. $$

Using the target signs $\sigma_k=2F(k)-1$, define

$$ P(z)=\sigma_0\prod_{j\in J}\left(j-\frac12-z\right). $$

This polynomial has degree $C$. Its sign at zero is $\sigma_0$, and its roots are the distinct half-integers $j-\frac12$ for $j\in J$. Thus it never vanishes at an integer weight. From weight $k-1$ to weight $k$, its sign changes exactly when $k\in J$. Consequently,

$$ \sigma_k P(k)\gt0 \qquad (0\leq k\leq n). $$

Substituting $z=x_1+\cdots+x_n$ gives a polynomial of total degree at most $C$ that strictly sign-represents $f$, so $\deg_{\pm}(f)\leq C$. If $C=0$, the empty product gives the nonzero constant $P=\sigma_0$, and the same argument applies.

**Lower bound.** Let $Q$ be any polynomial strictly sign-representing $f$, and let $d$ be its total degree. In each monomial, replace every positive power of a coordinate by its first power. This preserves values on the Boolean cube, since $x_i^m=x_i$ there for $m\geq1$, and cannot increase total degree. Continue to write $Q$ for the resulting multilinear polynomial, whose degree is at most $d$.

Let $\mathfrak{S}_n$ be the permutations of the $n$ coordinates and average over them:

$$ \overline Q(x)=\frac1{n!}\sum_{\pi\in\mathfrak{S}_n}Q(x_{\pi(1)},\ldots,x_{\pi(n)}). $$

The average is symmetric and multilinear, of degree at most $d$. For an input of weight $k$, every summand has strict sign $\sigma_k$, because permuting coordinates preserves weight and hence the label. The average therefore has the same strict sign.

Permuting coordinates carries any squarefree monomial of a given degree to any other of that degree. Invariance of $\overline Q$ makes their coefficients equal. With $r=\min(d,n)$, we can therefore write

$$ \overline Q(x)=\sum_{m=0}^{r}a_m e_m(x), \qquad e_m(x)=\sum_{\substack{S\subseteq\lbrace1,\ldots,n\rbrace\cr |S|=m}}\prod_{i\in S}x_i. $$

At an input of weight $k$, precisely $\binom{k}{m}$ of the products in $e_m$ equal one, and the others vanish. Thus $e_m(x)=\binom{k}{m}$. Define the univariate polynomial

$$ R(z)=\sum_{m=0}^{r}a_m\binom{z}{m}, \qquad \binom{z}{m}=\frac1{m!}\prod_{j=0}^{m-1}(z-j). $$

The empty product gives $\binom{z}{0}=1$. For integer weights, this formula agrees with the subset count, including zero when $m\gt k$. Hence $R(k)$ has strict sign $\sigma_k$ for every $0\leq k\leq n$, and $R$ is nonzero with degree at most $d$.

For each $j\in J$, the values $R(j-1)$ and $R(j)$ have opposite signs. The intermediate value theorem supplies a root in $(j-1,j)$. These intervals are disjoint, giving at least $C$ distinct roots. A nonzero polynomial of degree at most $d$ has at most $d$ distinct roots, so $d\geq C$.

Every polynomial strict sign representation has degree at least $C$, while the constructed witness has degree at most $C$. Therefore $\deg_{\pm}(f)=C$. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.13. Strict sign representation](../../definitions/13_strict_sign_representation.md).
- [Definition 1.14. Threshold degree](../../definitions/14_threshold_degree.md).
- [Definition 1.17. Symmetric functions](../../definitions/17_symmetric_functions.md).
- [Definition 1.18. Sign-change count](../../definitions/18_sign_change_count.md).

**Theorems**

None.
