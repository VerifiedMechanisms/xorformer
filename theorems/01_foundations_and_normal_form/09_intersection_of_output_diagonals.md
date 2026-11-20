# Theorem 1.9. Intersection of output diagonals

## Statement

Let $n\in\mathbb{Z}_{\geq2}$ and fix a one-head [model (Definition 1.1)](../../definitions/01_model.md). On a [two-coordinate restriction (Definition 1.11)](../../definitions/11_two_coordinate_restrictions.md), write $z(a,b)=y_1(x^{(a,b)})$ for the projected head output. Then

$$ [z(0,0),z(1,1)]\cap[z(0,1),z(1,0)]\neq\varnothing, $$

where $[u,v]=\lbrace(1-t)u+tv:0\leq t\leq1\rbrace$ denotes the closed line segment joining two vectors.

## Proof

### Additive decomposition

Suppress the head index. Its query $q=W_Q u_{=}$ is constant. At input position $k$, define the unnormalized weight $s_k(t)$ and projected value $\widehat v_k(t)$ for a bit $t$ by

$$ s_k(t)=\exp(q^\top W_K(e_t+p_k)), \qquad \widehat v_k(t)=W_O W_V(e_t+p_k). $$

For the query position, set

$$ s_{=}=\exp(q^\top W_Ku_{=}), \qquad \widehat v_{=}=W_O W_Vu_{=}. $$

Using the fixed-coordinate set $I$ and assignment $\xi$ from the restriction, collect the constant contributions:

$$ N_0=s_{=}\widehat v_{=}+\sum_{k\in I}s_k(\xi_k)\widehat v_k(\xi_k), \qquad D_0=s_{=}+\sum_{k\in I}s_k(\xi_k). $$

Linearity of the output map gives $z(a,b)=N(a,b)/D(a,b)$, where the projected numerator $N(a,b)$ and denominator $D(a,b)$ are

$$ N(a,b)=s_i(a)\widehat v_i(a)+s_j(b)\widehat v_j(b)+N_0, \qquad D(a,b)=s_i(a)+s_j(b)+D_0. $$

All weights are positive, so $D_0\gt0$ and $D(a,b)\gt0$. These formulas also apply when $I$ is empty.

### Diagonal identities

In either diagonal sum, each free position contributes its bit-zero term once and its bit-one term once, while the constant contribution appears twice. Therefore

$$ N(0,0)+N(1,1)=N(0,1)+N(1,0), \qquad D(0,0)+D(1,1)=D(0,1)+D(1,0). $$

### Common point

Define the positive scalar $S$ and vector $P$ by

$$ S=D(0,0)+D(1,1)=D(0,1)+D(1,0), \qquad P=\frac{N(0,0)+N(1,1)}{S}. $$

Using the diagonal identities and $N(a,b)=D(a,b)z(a,b)$ gives

$$ \begin{aligned} P&=\frac{D(0,0)}{S}z(0,0)+\frac{D(1,1)}{S}z(1,1) \cr &=\frac{D(0,1)}{S}z(0,1)+\frac{D(1,0)}{S}z(1,0). \end{aligned} $$

Each pair of weights is positive and sums to one. Thus $P$ belongs to both segments, as required. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.1. Model](../../definitions/01_model.md).
- [Definition 1.11. Two-coordinate restrictions](../../definitions/11_two_coordinate_restrictions.md).

**Theorems**

None.
