# Theorem 1.6. Zero-head constants

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $f:\lbrace0,1\rbrace^n\to\lbrace0,1\rbrace$. Its [head complexity (Definition 1.5)](../../definitions/05_head_complexity.md) $H^{\ast}(f)$ satisfies

$$ H^{\ast}(f)=0\quad\Longleftrightarrow\quad f\text{ is constant}. $$

## Proof

If $H^{\ast}(f)=0$, a zero-head [model](../../definitions/01_model.md) computes $f$. Its query residual is $r(x)=u_{=}$, so its [score](../../definitions/02_score.md) $\Phi(x)=w^\top u_{=}-\tau$ is constant. The [classification rule](../../definitions/03_classification.md) therefore gives a constant Boolean function.

Conversely, suppose $f(x)=c$ for every input, with $c\in\lbrace0,1\rbrace$. Choose zero heads, model and head dimensions one, zero embeddings, $w=0$, and $\tau=1-2c$. The resulting score is $\Phi(x)=2c-1$, which classifies $f$. Thus zero is a feasible head count, and the minimum is zero. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.1. Model](../../definitions/01_model.md).
- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.3. Classification](../../definitions/03_classification.md).
- [Definition 1.5. Head complexity](../../definitions/05_head_complexity.md).

**Theorems**

None.
