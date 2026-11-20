# Theorem 1.3. Coefficient admissibility

## Statement

Let $n\in\mathbb{Z}_{\geq1}$. Expanding an [atom (Definition 1.6)](../../definitions/06_atoms.md) $\phi$ gives the affine coefficients

$$ A_i=\rho_i((\alpha-1)m_i+\alpha\delta), \qquad b=\eta+\sum_i\rho_i m_i, \qquad C_i=\rho_i(\alpha-1), \qquad d=\gamma+\sum_i\rho_i, $$

and the identity

$$ \phi(x)=\frac{A^\top x+b}{C^\top x+d}, \qquad x\in\lbrace0,1\rbrace^n. $$

A prescribed coefficient tuple $(A,b,C,d)$ is obtained by this map if and only if it is [admissible (Definition 1.8)](../../definitions/08_admissible_ratios.md).

## Proof

### Expansion and necessity

For each Boolean coordinate,

$$ \alpha^{x_i}=1+(\alpha-1)x_i, \qquad \alpha^{x_i}(m_i+\delta x_i)=m_i+((\alpha-1)m_i+\alpha\delta)x_i. $$

These identities give the coefficient map and the ratio identity. The denominator is positive because every term in the atom denominator is positive.

All $C_i$ have the sign of $\alpha-1$. If $C=0$, positivity of the $\rho_i$ forces $\alpha=1$, and then $A_i=\rho_i\delta$. The numerator slopes therefore share a strict sign or all vanish.

### Constructive converse

Fix an admissible tuple $(A,b,C,d)$. Positivity at the all-zero input gives $d\gt0$.

**Nonconstant denominator.** In either strict sign case, use

$$ \rho_i=\frac{C_i}{\alpha-1}, \qquad \gamma=d-\sum_i\rho_i, \qquad \delta=0, \qquad m_i=\frac{A_i}{C_i}, \qquad \eta=b-\sum_i\rho_i m_i. $$

If every $C_i\gt0$, put $S=\sum_i C_i$ and choose $\alpha=2+S/d$. Then $\rho_i\gt0$ and

$$ \sum_i\rho_i=\frac{S}{1+S/d}=\frac{dS}{d+S}\lt d, $$

so $\gamma\gt0$.

If every $C_i\lt0$, put $S=-\sum_i C_i$. Positivity at the all-one input gives $0\lt S\lt d$. Choose $\alpha=(d-S)/(2d)$, so $0\lt\alpha\lt1$. Again $\rho_i\gt0$, and

$$ \sum_i\rho_i=\frac{2dS}{d+S}\lt d, $$

so $\gamma\gt0$. In both cases the coefficient map gives $C_i=\rho_i(\alpha-1)$ and $A_i=\rho_i(\alpha-1)m_i$, and the definitions of $\gamma,\eta$ recover $d,b$ exactly.

**Constant denominator with nonzero numerator slopes.** Here $C=0$, and admissibility gives a sign $\sigma\in\lbrace-1,1\rbrace$ such that $a_i=\sigma A_i\gt0$ for every $i$. Set

$$ q=1+\frac{\sum_i a_i}{d}, \qquad \alpha=1, \qquad \rho_i=\frac{a_i}{q}, \qquad \delta=\sigma q, \qquad m_i=0, \qquad \eta=b, \qquad \gamma=d-\sum_i\rho_i. $$

All $\rho_i$ are positive, their sum is strictly less than $d$, and hence $\gamma\gt0$. The coefficient map gives $C_i=0$ and $A_i=\rho_i\delta$, with the prescribed $b,d$.

**Constant numerator and denominator.** If $A=C=0$, take

$$ \alpha=1, \qquad \delta=0, \qquad m_i=0, \qquad \eta=b, \qquad \rho_i=\gamma=\frac{d}{n+1}. $$

These parameters satisfy all positivity conditions. Their denominator constant is $(n+1)d/(n+1)=d$, their numerator constant is $b$, and both slope vectors vanish. This exhausts the admissible cases. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.6. Atoms](../../definitions/06_atoms.md).
- [Definition 1.8. Admissible ratios](../../definitions/08_admissible_ratios.md).

**Theorems**

None.
