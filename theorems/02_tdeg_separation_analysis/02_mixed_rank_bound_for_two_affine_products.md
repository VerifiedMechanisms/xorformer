# Theorem 2.2. Mixed-rank bound for two affine products

## Statement

Let $L_1,R_1,L_2,R_2$ be [real affine forms (Definition 1.14)](../../definitions/14_real_affine_forms.md) on $\mathbb{R}^5\times\mathbb{R}^5$, and set

$$ g(x,y)=L_1(x,y)R_1(x,y)+L_2(x,y)R_2(x,y). $$

For any five sign vectors $s^{(1)},\ldots,s^{(5)}\in\lbrace-1,+1\rbrace^5$, there is a matrix $M\in\mathbb{R}^{5\times5}$ such that the [mixed antipodal difference (Definition 1.23)](../../definitions/23_mixed_antipodal_difference.md) $\Delta g$ satisfies

$$ \Delta g(x,s^{(j)})=\sum_{i=1}^{5}M_{ij}x_i, \qquad x\in\lbrace-1,+1\rbrace^5, \quad j\in\lbrace1,\ldots,5\rbrace, $$

and

$$ \mathrm{rank}(M)\leq4. $$

## Proof

Write two affine forms as

$$ L(x,y)=\ell_0+a_L^\top x+b_L^\top y, \qquad R(x,y)=r_0+a_R^\top x+b_R^\top y, $$

where the coefficient vectors belong to $\mathbb{R}^5$. Expanding the product gives

$$ \begin{aligned} LR&=\ell_0r_0+(r_0a_L+\ell_0a_R)^\top x+(r_0b_L+\ell_0b_R)^\top y \cr &\quad +(a_L^\top x)(a_R^\top x)+(b_L^\top y)(b_R^\top y) \cr &\quad +(a_L^\top x)(b_R^\top y)+(a_R^\top x)(b_L^\top y). \end{aligned} $$

In the mixed difference, terms depending on only one block cancel. Each of the last two terms changes sign when either block is negated, so its four signed contributions agree. Hence

$$ \Delta(LR)(x,y)=4\left((a_L^\top x)(b_R^\top y)+(a_R^\top x)(b_L^\top y)\right). $$

Apply this identity to both products defining $g$. For each $j$, define the column $M_{\cdot j}$ by

$$ M_{\cdot j}=4\sum_{h=1}^{2}\left(a_{L_h}(b_{R_h}^\top s^{(j)})+a_{R_h}(b_{L_h}^\top s^{(j)})\right). $$

The mixed difference is linear in $g$, so these columns satisfy the asserted identity. Every column lies in the span of $a_{L_1},a_{R_1},a_{L_2},a_{R_2}$. The column space therefore has dimension at most four, proving $\mathrm{rank}(M)\leq4$. $\blacksquare$

## Dependencies

**Definitions**

- [Definition 1.14. Real affine forms](../../definitions/14_real_affine_forms.md).
- [Definition 1.23. Mixed antipodal difference](../../definitions/23_mixed_antipodal_difference.md).

**Theorems**

None.
