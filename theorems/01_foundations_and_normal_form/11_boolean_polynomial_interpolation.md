# Theorem 1.11. Boolean polynomial interpolation

## Statement

Let $n\in\mathbb{Z}_{\geq1}$. Every function $g:\lbrace0,1\rbrace^n\to\mathbb{R}$ has a multilinear polynomial representation $P\in\mathbb{R}[x_1,\ldots,x_n]$ of total degree at most $n$, satisfying

$$ P(x)=g(x)\qquad\text{for every }x\in\lbrace0,1\rbrace^n. $$

Here multilinear means that each variable has degree at most one. In particular, every Boolean function $f$ on this cube has finite [threshold degree (Definition 1.14)](../../definitions/14_threshold_degree.md) $\deg_{\pm}(f)$, with

$$ 0\leq\deg_{\pm}(f)\leq n. $$

## Proof

For each vertex $a\in\lbrace0,1\rbrace^n$, define

$$ B_a(x)=\prod_{i=1}^{n}\bigl(a_i x_i+(1-a_i)(1-x_i)\bigr). $$

On a Boolean input $x$, the factor for coordinate $i$ equals one when $x_i=a_i$ and zero otherwise. Thus $B_a(x)$ equals one at $x=a$ and zero at every other vertex. Consequently,

$$ P(x)=\sum_{a\in\lbrace0,1\rbrace^n}g(a)B_a(x) $$

agrees with $g$ at every vertex. Each factor in $B_a$ is affine in a single coordinate, with different factors using different coordinates. Hence every $B_a$, and therefore $P$, is multilinear and has total degree at most $n$.

Apply this construction to $g(x)=2f(x)-1$. The resulting polynomial equals one on true inputs and minus one on false inputs, so it is a [strict sign representation (Definition 1.13)](../../definitions/13_strict_sign_representation.md) of $f$. Its degree is at most $n$. The feasible degrees are therefore a nonempty set of nonnegative integers containing a value at most $n$, which proves the threshold-degree bounds. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.13. Strict sign representation](../../definitions/13_strict_sign_representation.md).
- [Definition 1.14. Threshold degree](../../definitions/14_threshold_degree.md).

**Theorems**

None.
