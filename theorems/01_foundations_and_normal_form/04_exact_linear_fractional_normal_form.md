# Theorem 1.4. Exact linear-fractional normal form

## Statement

Let $n\in\mathbb{Z}_{\geq1}$ and $H\in\mathbb{Z} _{\geq0}$. The [scores](../../definitions/02_score.md) $\Phi$ realizable with $H$ heads are exactly the functions

$$ \Phi(x)=c+\sum_{h=1}^{H}\frac{A_h^\top x+b_h}{C_h^\top x+d_h}, \qquad x\in\lbrace0,1\rbrace^n, $$

where $c\in\mathbb{R}$ and every tuple $(A_h,b_h,C_h,d_h)$ is [admissible](../../definitions/07_admissible_ratios.md). For $H=0$, the sum is empty.

## Proof

Given a score $\Phi$ realizable with $H$ heads, [Theorem 1.1](01_head_to_atom_reduction.md) expresses it as a constant plus $H$ atoms. Apply [Theorem 1.3](03_coefficient_admissibility.md) to each atom to obtain the required admissible ratios.

Conversely, Theorem 1.3 realizes each prescribed admissible tuple as the coefficients of an atom. [Theorem 1.2](02_atom_sum_realization.md) then realizes their sum plus $c$ with $H$ heads. Each step preserves the score at every input and the number of terms, including empty sums. $\blacksquare$

## Dependencies

**Definitions**

- [Score](../../definitions/02_score.md).
- [Admissible ratios](../../definitions/07_admissible_ratios.md).

**Theorems**

- [Theorem 1.1. Head-to-atom reduction](01_head_to_atom_reduction.md).
- [Theorem 1.2. Atom-sum realization](02_atom_sum_realization.md).
- [Theorem 1.3. Coefficient admissibility](03_coefficient_admissibility.md).
