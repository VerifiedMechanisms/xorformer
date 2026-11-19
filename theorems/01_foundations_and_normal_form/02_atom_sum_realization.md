# Theorem 1.2. Atom-sum realization

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $H\in\mathbb{Z} _{\geq0}$, let $\phi_1,\ldots,\phi_H$ be [atoms (Definition 1.6)](../../definitions/06_atoms.md) on $\lbrace0,1\rbrace^n$, and let $c\in\mathbb{R}$. The [score (Definition 1.2)](../../definitions/02_score.md) $\Phi$ defined by

$$ \Phi(x)=c+\sum_{h=1}^{H}\phi_h(x) $$

is realizable with $H$ heads. For $H\geq1$, one can choose $d_{\mathrm{model}}=d_{\mathrm{head}}=4H$; for $H=0$, both dimensions can be one.

## Proof

For $H=0$, take both dimensions to be one, choose zero embeddings, and set $w=0$, $\tau=-c$.

For $H\geq1$, identify both spaces in the [model](../../definitions/01_model.md) with $\mathbb{R}^{4H}$ and choose an orthonormal basis consisting of $q_h,k_h,v_h,o_h$ for $1\leq h\leq H$. Write the parameters of atom $h$ with a head subscript. Set

$$ e_0=0, \qquad e_1=\sum_h((\log\alpha_h)k_h+\delta_h v_h), \qquad e_{=}=\sum_h\left(q_h+(\log\gamma_h)k_h+\frac{\eta_h}{\gamma_h}v_h\right), $$

$$ p_i=\sum_h((\log\rho_{h,i})k_h+m_{h,i}v_h), \qquad p_{=}=0. $$

For head $h$, define the following nonzero actions, with every other basis vector sent to zero:

$$ W_Q^{(h)}q_h=q_h, \qquad W_K^{(h)}k_h=q_h, \qquad W_V^{(h)}v_h=o_h, \qquad W_O^{(h)}o_h=o_h. $$

The query vector is $q_h$. The input logits are $\log\rho_{h,i}+x_i\log\alpha_h$, and the query logit is $\log\gamma_h$. The projected input values are $(m_{h,i}+\delta_h x_i)o_h$, and the projected query value is $(\eta_h/\gamma_h)o_h$. Therefore

$$ y_h(x)=\frac{\eta_h+\sum_i\rho_{h,i}\alpha_h^{x_i}(m_{h,i}+\delta_h x_i)}{\gamma_h+\sum_i\rho_{h,i}\alpha_h^{x_i}}o_h=\phi_h(x)o_h. $$

Choose $w=\sum_h o_h$ and $\tau=-c$. The query embedding has zero component in every output direction, so $w^\top u_{=}=0$. It follows that

$$ w^\top r(x)-\tau=c+\sum_h\phi_h(x). $$

This realizes the prescribed score with the stated dimensions. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.1. Model](../../definitions/01_model.md).
- [Definition 1.2. Score](../../definitions/02_score.md).
- [Definition 1.6. Atoms](../../definitions/06_atoms.md).

**Theorems**

None.
