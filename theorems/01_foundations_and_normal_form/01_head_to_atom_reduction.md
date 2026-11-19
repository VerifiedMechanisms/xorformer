# Theorem 1.1. Head-to-atom reduction

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $H\in\mathbb{Z} _{\geq0}$. Every [score (Definition 1.2)](../../definitions/02_score.md) $\Phi$ realizable with $H$ heads has the form

$$ \Phi(x)=c+\sum_{h=1}^{H}\phi_h(x), \qquad x\in\lbrace0,1\rbrace^n, $$

where $c\in\mathbb{R}$ and each $\phi_h$ is an [atom (Definition 1.6)](../../definitions/06_atoms.md).

## Proof

Fix realizing [model parameters](../../definitions/01_model.md), a readout $w$, and threshold $\tau$. For one head, suppress its index and set $q=W_Q u_{=}$. Define

$$ \rho_i=\exp(q^\top W_K(e_0+p_i)), \qquad \alpha=\exp(q^\top W_K(e_1-e_0)), \qquad \gamma=\exp(q^\top W_Ku_{=}). $$

These parameters are positive. Since $e_{x_i}=e_0+x_i(e_1-e_0)$, the unnormalized input weight is $\rho_i\alpha^{x_i}$ and the query weight is $\gamma$.

Define the scalar value parameters by

$$ m_i=w^\top W_O W_V(e_0+p_i), \qquad \delta=w^\top W_O W_V(e_1-e_0), \qquad \eta=\gamma w^\top W_O W_Vu_{=}. $$

The projected input value, after applying the readout, is $m_i+\delta x_i$. The query contributes $\eta$ to the numerator. Thus the scalar head contribution is exactly

$$ w^\top y(x)=\frac{\eta+\sum_{i=1}^{n}\rho_i\alpha^{x_i}(m_i+\delta x_i)}{\gamma+\sum_{i=1}^{n}\rho_i\alpha^{x_i}}. $$

Applying this to each head and expanding the residual gives

$$ \Phi(x)=w^\top u_{=}-\tau+\sum_{h=1}^{H}w^\top y_h(x)=c+\sum_{h=1}^{H}\phi_h(x), \qquad c=w^\top u_{=}-\tau. $$

For $H=0$, the head sum is empty. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.1. Model](../../definitions/01_model.md).
- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.6. Atoms](../../definitions/06_atoms.md).

**Theorems**

None.
