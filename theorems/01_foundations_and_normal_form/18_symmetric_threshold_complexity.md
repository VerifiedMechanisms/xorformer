# Theorem 1.18. Symmetric threshold complexity

## Statement

Let $n,t$ be integers with $n\geq1$ and $1\leq t\leq n$. The [symmetric threshold (Definition 1.18)](../../definitions/18_symmetric_thresholds.md) $T_{n,t}$ has [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md)

$$ H^{\ast}(T_{n,t})=1. $$

It can be computed with one head, all positional embeddings zero, and [model and head dimensions (Definition 1.1)](../../definitions/01_model.md)

$$ d_{\mathrm{model}}=d_{\mathrm{head}}=2. $$

In particular, the OR, AND, and majority functions from Definition 1.18 satisfy

$$ H^{\ast}(\mathrm{OR}_n)=H^{\ast}(\mathrm{AND}_n)=H^{\ast}(\mathrm{MAJORITY}_n)=1. $$

## Proof

### Exact head count

Write $T_{n,t}(x)=F(|x|)$. The weight sequence $F$ is zero for $0\leq s\lt t$ and one for $t\leq s\leq n$. It changes label exactly once, between weights $t-1$ and $t$, so its [sign-change count (Definition 1.17)](../../definitions/17_sign_change_count.md) is $C(F)=1$.

By [Theorem 1.17](17_exact_symmetric_head_complexity.md), $H^{\ast}(T_{n,t})=C(F)=1$. The stated examples correspond to $t=1,n,\lceil n/2\rceil$, respectively, all of which lie between one and $n$.

### Two-dimensional realization

Take both dimensions equal to two, with orthonormal basis $u=(1,0)$ and $v=(0,1)$. Set

$$ e_0=0, \qquad e_1=u+v, \qquad e_{=}=u, \qquad p_i=p_{=}=0. $$

Use one head with maps

$$ W_Q=W_K=\begin{pmatrix}1&0\cr0&0\end{pmatrix}, \qquad W_V=\begin{pmatrix}0&0\cr0&1\end{pmatrix}, \qquad W_O=I_2. $$

The query vector is $u$. An input one has logit one and value $v$; an input zero has logit zero and value zero. The query position has logit one and value zero. With $\alpha=\exp(1)$, the projected head output on an input of weight $k$ is

$$ y_1(x)=s(k)v, \qquad s(k)=\frac{\alpha k}{(n-k)+\alpha k+\alpha}=\frac{\alpha k}{n+\alpha+(\alpha-1)k}. $$

The denominator is positive. For every integer $0\leq k\lt n$,

$$ s(k+1)-s(k)=\frac{\alpha(n+\alpha)}{\bigl(n+\alpha+(\alpha-1)k\bigr)\bigl(n+\alpha+(\alpha-1)(k+1)\bigr)}\gt0. $$

Choose $w=v$ and $\tau=(s(t-1)+s(t))/2$. The query residual is $r(x)=u+s(k)v$, so the [score (Definition 1.2)](../../definitions/02_score.md) is

$$ \Phi(x)=w^\top r(x)-\tau=s(k)-\tau. $$

Strict monotonicity makes this score negative when $k\lt t$ and positive when $k\geq t$. It therefore [classifies (Definition 1.3)](../../definitions/03_classification.md) $T_{n,t}$, proving the dimension and positional-embedding guarantees. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.1. Model](../../definitions/01_model.md).
- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).
- [Definition 1.17. Sign-change count](../../definitions/17_sign_change_count.md).
- [Definition 1.18. Symmetric thresholds](../../definitions/18_symmetric_thresholds.md).

**Theorems**

- [Theorem 1.17. Exact symmetric head complexity](17_exact_symmetric_head_complexity.md).
