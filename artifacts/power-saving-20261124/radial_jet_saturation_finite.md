# A finite certificate for simultaneous radial jet saturation

## Status

This is a finite exact algebraic result for six Boolean variables and eight fixed radial directions. The determinant certificate is verified modulo an integer and is used with separate rank bounds over the rationals. It is stronger than an unsupported transfer of a difference of modular ranks to characteristic zero. It is not a sign-count theorem, a proof about arbitrary finite-scale denominators, or the requested lower bound on the original worst-case head complexity. No Lean formalization of this result is claimed.

## Statement

Put $X=\lbrace 0,1\rbrace^6$. The file `radial_jet_saturation_certificate.json` specifies eight vectors $c_h\in\mathbb Z_{\gt 0}^6$. Set $C_h(x)=\sum_{i=1}^6c_{hi}x_i$ and consider the rational table space over $\mathbb Q(t)$

$$ V(t)=\mathrm{span}_{\mathbb Q(t)}\left\lbrace 1,\frac{x_i}{1+tC_h(x)}:1\leq i\leq6,1\leq h\leq8\right\rbrace. $$

There is a 48-dimensional rational vector space $U\subseteq\mathbb Q^X$ such that every $u\in U$ is the order-three leading coefficient of a score

$$ G(t,x)=\sum_{j=0}^{2}t^j\left(a_j+\sum_{h=1}^8\sum_{i=1}^6\frac{b_{jhi}x_i}{1+tC_h(x)}\right),\qquad G(t,x)=t^3u(x)+O(t^4). $$

Every member of $U$ vanishes at the zero vertex. The space spanned by $1$ and $U$ is the entire initial table space of $V(t)$, defined as the span of leading coefficients of its nonzero rational table germs. In particular, this is simultaneous saturation at one common leading order with numerator polynomial degree two, rather than only a sum of separate leading images occurring at different orders.

## Exact coefficient matrices

Let $M_k$ be the $64$ by $49$ integer matrix whose non-bias columns are the tables $x_i(-C_h(x))^k$. Its bias column is $1$ for $k=0$ and zero otherwise. Define the $64$ by $147$ block matrix

$$ T_k=\left[M_k\quad M_{k-1}\quad M_{k-2}\right], $$

with $M_j=0$ for $j\lt0$. These are precisely the Taylor coefficient maps for the degree-two numerator family. Write $T_{\lt3}$ for the stack of $T_0,T_1,T_2$ and $T_{\leq3}$ for the stack including $T_3$. The required leading image is

$$ U=T_3\left(\ker T_{\lt3}\right),\qquad \dim U=\mathrm{rank}T_{\leq3}-\mathrm{rank}T_{\lt3}. $$

This equality is the rank-nullity theorem applied to the two stacked maps over $\mathbb Q$.

## Structural bounds in characteristic zero

Every column of $T_k$ is the restriction of a polynomial in the input variables of total degree at most $k+1$. On the Boolean cube, multilinear reduction gives a table space of dimension at most $\sum_{j=0}^{k+1}\binom6j$. Consequently

$$ \mathrm{rank}_{\mathbb Q}T_{\lt3}\leq7+22+42=71. $$

This is an upper bound in characteristic zero, independent of the modular calculation.

The space $U$ has dimension at most 48. Every table in it vanishes at zero because $G(t,0)$ is a polynomial of degree at most two and its coefficients through order two vanish. If $u_1,\ldots,u_s$ are independent members of $U$, choose germs $G_j=t^3u_j+O(t^4)$ producing them. The tables $1,u_1,\ldots,u_s$ are independent. A corresponding nonzero table minor shows that $1,G_1,\ldots,G_s$ are independent over $\mathbb Q(t)$: its first nonzero coefficient is $t^{3s}$ times the nonzero minor of $1,u_1,\ldots,u_s$. These rational tables belong to $V(t)$, which has at most 49 displayed generators. Hence $s+1\leq49$.

The same minor argument bounds the dimension of the whole initial table space by 49. Once $1$ and the 48 independent vectors below have been obtained, they therefore span that space.

## The finite determinant certificate

The certificate gives 119 row indices and 119 column indices of $T_{\leq3}$. The corresponding integer square minor has nonzero determinant modulo 65521. The exact residue is recorded in the JSON file. Thus this determinant is a nonzero integer and

$$ \mathrm{rank}_{\mathbb Q}T_{\leq3}\geq119. $$

Combining this lower bound with the separate structural upper bound gives $\dim U\geq119-71=48$. The previous argument gives equality. It also follows that the lower stack has rank exactly 71 and the full stack has rank exactly 119.

The program `certify_radial_jet_saturation.py` reconstructs the integer coefficient matrices modulo 65521, selects the minor, and verifies its determinant using modular Gaussian elimination. The file fixes the random seed only to generate the displayed integer directions; all claims concern those explicit integers, not a probabilistic event. Each selected pivot is checked to be invertible. A nonzero determinant residue proves that the integer determinant is nonzero regardless of whether primality is separately established.

## A limited generic consequence

The selected determinant is a polynomial with integer coefficients in the 48 direction entries. Its displayed nonzero value proves that it is not the zero polynomial. Therefore its nonvanishing set is a nonempty Zariski open set. The structural upper bounds hold for every direction list. The same saturation statement consequently holds for every direction list in that open set, including an ordinary open neighborhood of the displayed positive list.

This generic statement concerns the fixed pair of integers $n=6$ and $H=8$. It does not supply an asymptotic jet-degree bound, does not control exceptional direction sets, and does not move an arbitrary original-model sign table to a radial limit. Even a general generic radial saturation theorem would still require a separate sign-preserving bridge from arbitrary finite-scale representations.
