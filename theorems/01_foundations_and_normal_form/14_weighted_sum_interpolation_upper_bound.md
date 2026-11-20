# Theorem 1.14. Weighted-sum interpolation upper bound

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and let a [positive weighted statistic (Definition 1.15)](../../definitions/15_positive_weighted_statistics.md) $t$ have image $T$ of size $M$. For every function $G:T\to\mathbb{R}$, the [score (Definition 1.2)](../../definitions/02_score.md) $\Phi$ given by

$$ \Phi(x)=G(t(x)) $$

is realizable with $M-1$ heads and [model and head dimensions (Definition 1.1)](../../definitions/01_model.md)

$$ d_{\mathrm{model}}=d_{\mathrm{head}}=M+2. $$

In particular, if $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$ satisfies $f(x)=F(t(x))$ for some $F:T\to\lbrace0,1\rbrace$, then its [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$ satisfies

$$ H^{\ast}(f)\leq M-1. $$

## Proof

All values in $T$ are nonnegative. The set contains zero and $t(1,\ldots,1)\gt0$, so $M\geq2$.

### Interpolation

Choose distinct positive numbers $r_1,\ldots,r_{M-1}$. We show that the functions

$$ 1,\qquad \frac{1}{s+r_1},\qquad\ldots,\qquad\frac{1}{s+r_{M-1}} $$

form a basis of the real-valued functions on $T$. Suppose

$$ a_0+\sum_{j=1}^{M-1}\frac{a_j}{s+r_j}=0\qquad\text{for every }s\in T. $$

Every denominator is positive on $T$. Multiplying by their product shows that the polynomial

$$ Q(s)=a_0\prod_{j=1}^{M-1}(s+r_j)+\sum_{j=1}^{M-1}a_j\prod_{\substack{1\leq\ell\leq M-1\cr \ell\neq j}}(s+r_\ell) $$

vanishes at all $M$ distinct points of $T$. Its degree is at most $M-1$, so $Q$ is the zero polynomial. For each $j$, evaluating this polynomial identity at $s=-r_j$ gives

$$ a_j\prod_{\substack{1\leq\ell\leq M-1\cr \ell\neq j}}(r_\ell-r_j)=0. $$

The shifts are distinct, so every factor in the product is nonzero; an empty product equals one. Hence $a_j=0$ for all $j\geq1$. The original relation then gives $a_0=0$.

Thus the displayed functions are linearly independent. The space of real-valued functions on the $M$-point set $T$ has dimension $M$, so these $M$ functions form a basis.

### Realization with prescribed dimensions

Let $\lambda=(\lambda_1,\ldots,\lambda_n)$ be the weight vector of $t$, and set $H=M-1$ and $\Lambda=\sum_i\lambda_i$. For $1\leq j\leq H$, define

$$ \alpha_j=1+\frac{1+\Lambda}{r_j}, \qquad g_j(s)=\frac{\alpha_j s}{1+\Lambda+(\alpha_j-1)s}=\frac{\alpha_j}{\alpha_j-1}\left(1-\frac{r_j}{s+r_j}\right). $$

Since $\alpha_j\gt1$ and $r_j\gt0$, each reciprocal in the interpolation basis is a linear combination of $1$ and $g_j$, and conversely. Thus $1,g_1,\ldots,g_H$ also form a basis on $T$. Choose real coefficients $\beta_0,\ldots,\beta_H$ with

$$ G(s)=\beta_0+\sum_{j=1}^{H}\beta_j g_j(s)\qquad\text{for every }s\in T. $$

Take both dimensions equal to $M+2$ and choose an orthonormal basis $q,v,u,o_1,\ldots,o_H$. Set

$$ e_0=0, \qquad e_1=u, \qquad e_{=}=q, \qquad p_i=(\log\lambda_i)v, \qquad p_{=}=0. $$

For head $j$, give the query, key, and value maps the following actions, sending all unlisted basis vectors to zero:

$$ W_Q^{(j)}q=q, \qquad W_K^{(j)}v=q, \qquad W_K^{(j)}u=(\log\alpha_j)q, \qquad W_V^{(j)}u=o_j. $$

Set $W_O^{(j)}$ to the identity. The query vector is $q$. At input position $i$, the logit is $\log\lambda_i+x_i\log\alpha_j$ and the value is $x_i o_j$. The query position has logit zero and value zero. Consequently,

$$ y_j(x)=\frac{\alpha_j\sum_i\lambda_i x_i}{1+\sum_i\lambda_i\alpha_j^{x_i}}o_j=\frac{\alpha_j t(x)}{1+\Lambda+(\alpha_j-1)t(x)}o_j=g_j(t(x))o_j. $$

The denominator is at least $1+\Lambda\gt0$. Choose

$$ w=\sum_{j=1}^{H}\beta_j o_j, \qquad \tau=-\beta_0. $$

The query residual is $r(x)=q+\sum_j y_j(x)$, and $w^\top q=0$. The full score is therefore

$$ \Phi(x)=w^\top r(x)-\tau=\beta_0+\sum_{j=1}^{H}\beta_j g_j(t(x))=G(t(x)). $$

This proves exact score realization with the stated head count and dimensions.

### Boolean classification

For the Boolean consequence, take $G(s)=2F(s)-1$. The realized score is one on true inputs and minus one on false inputs, so it [classifies (Definition 1.3)](../../definitions/03_classification.md) $f$. Thus $M-1$ is a feasible head count and $H^{\ast}(f)\leq M-1$. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.1. Model](../../definitions/01_model.md).
- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.15. Positive weighted statistics](../../definitions/15_positive_weighted_statistics.md).

**Theorems**

None.
