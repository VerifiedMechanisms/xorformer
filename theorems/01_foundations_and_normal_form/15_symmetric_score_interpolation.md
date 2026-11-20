# Theorem 1.15. Symmetric score interpolation

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $G:\lbrace0,1,\ldots,n\rbrace\to\mathbb{R}$. Using [Hamming weight (Definition 1.17)](../../definitions/17_symmetric_functions.md) $|x|$, define the [score (Definition 1.2)](../../definitions/02_score.md) $\Phi$ by

$$ \Phi(x)=G(|x|). $$

This score is realizable with $n$ heads, all positional embeddings zero, and [model and head dimensions (Definition 1.1)](../../definitions/01_model.md)

$$ d_{\mathrm{model}}=d_{\mathrm{head}}=n+2. $$

## Proof

Set every weight $\lambda_i=1$ in the [positive weighted statistic (Definition 1.15)](../../definitions/15_positive_weighted_statistics.md) $t$. Then

$$ t(x)=|x|, \qquad T=\lbrace0,1,\ldots,n\rbrace, \qquad M=n+1. $$

Apply the explicit construction in [Theorem 1.14](14_weighted_sum_interpolation_upper_bound.md) to $G$. It realizes $G(|x|)$ with $H=M-1=n$ heads and both dimensions equal to $M+2=n+3$. We remove its unused positional coordinate to obtain the stated dimensions.

The construction uses an orthonormal basis $q,v,u,o_1,\ldots,o_n$. Its token embeddings are $e_0=0$, $e_1=u$, and $e_{=}=q$. All positional embeddings vanish, since $p_i=(\log1)v=0$ and $p_{=}=0$. Its readout vector is a linear combination of $o_1,\ldots,o_n$.

Consequently, every embedding and the readout lie in

$$ V=\mathrm{span}\lbrace q,u,o_1,\ldots,o_n\rbrace. $$

The query, key, value, and output maps in that construction all send $V$ into $V$. Restricting them to $V$ therefore leaves every intermediate vector in the same space and preserves all inner products. The logits, attention weights, projected outputs, query residual, and final score remain unchanged.

Using the displayed orthonormal basis of $V$ gives both dimensions equal to $n+2$. The head count remains $n$, all positional embeddings remain zero, and the score equals $G(|x|)$ on every input. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.1. Model](../../definitions/01_model.md).
- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.15. Positive weighted statistics](../../definitions/15_positive_weighted_statistics.md).
- [Definition 1.17. Symmetric functions](../../definitions/17_symmetric_functions.md).

**Theorems**

- [Theorem 1.14. Weighted-sum interpolation upper bound](14_weighted_sum_interpolation_upper_bound.md).
