# Many strict truth tables approach one full-rank boundary point

## Statement and scope

For every integer $m\geq1$, put $n=2m+2$. There are at least $2^{m^2}$ distinct strict truth tables with all of the following properties.

Each table is represented by one original head. For every fixed $\varepsilon\gt0$, it has a one-head representation with denominator $B_\varepsilon(x)=\varepsilon+|x|$. Every representation of that same table using only this fixed denominator, even with arbitrary numerator refitting, bias, and repeated copies, has relative margin at most

$$ \frac{\varepsilon}{4+3\varepsilon}. $$

The compact normalized feature matrix retains an identity submatrix of size $n+1$ throughout and at the limit $\varepsilon=0$. All the displayed normalized witnesses converge to the *same* negative point mass at the zero vertex. Nevertheless each truth table has a different-denominator one-head representation with relative margin at least $\exp(-O(n))$.

This is a written finite construction, not an unrestricted margin lower bound or a kernel-checked counting theorem. It strengthens the [three-bit boundary example](margin_repair_full_rank_boundary.md) by showing that one full-rank boundary point admits exponentially many in $n^2$ eventual strict tables. It does not permit multiplying that count independently across arbitrary head families.

## Explicit tables

Split the coordinates into address bits $u_0,\ldots,u_{m-1}$, token bits $v_1,\ldots,v_m$, and two gadget bits $y_1,y_2$. For each integer vector

$$ a=(a_1,\ldots,a_m)\in\lbrace1,\ldots,2^m\rbrace^m, $$

define the affine numerator

$$ A_a(x)=10\sum_{j=1}^m a_jv_j-10\sum_{i=0}^{m-1}2^iu_i+3y_1+3y_2-5. $$

All its cube values are nonzero integers. The possible residues modulo ten are five, eight, and one, according to whether $y_1+y_2$ is zero, one, or two. Thus $F_a=\mathrm{sign}(A_a)$ is strict on the whole cube.

The tables are distinct. If $a_j\lt a'_j$, choose the token vector $v=e_j$, set both gadget bits to zero, and let the address encode the integer $a_j$. This address exists because $a_j\lt a'_j\leq2^m$. The two numerator values at this vertex are respectively $-5$ and $10(a'_j-a_j)-5\geq5$. Hence $F _a\neq F _{a'}$. There are exactly $(2^m)^m=2^{m^2}$ choices of $a$.

For every positive $\varepsilon$, the ratio $A_a/B_\varepsilon$ has these same strict signs. The denominator has positive constant term and strictly positive slopes, so it is an admissible original head with arbitrary affine numerator.

## All refits over the fixed denominator have tiny margin

On the two-dimensional gadget face obtained by setting every $u_i,v_j$ to zero, the numerator values at the origin, gadget singletons, and gadget pair are

$$ -5,\qquad -2,\qquad -2,\qquad1. $$

Therefore every representation of $F_a$ has negative scores at those first three vertices and positive score at the pair. Suppose the representation has only denominator $B_\varepsilon$, allowing copies. Combine its numerators and absorb the bias to obtain an affine ratio

$$ S(x)=\frac{\alpha+\sum_i\beta_i x_i}{\varepsilon+|x|}. $$

Let $M$ be the original amplitude sum, including the absolute bias, and let $\mu$ be the smallest signed score. The triangle inequality gives $\|S\|_\infty\leq M$. The exact two-singleton and one-pair argument in the three-bit example applies on the gadget face and gives

$$ \mu(4+3\varepsilon)\leq-\alpha\leq\varepsilon M. $$

Consequently the relative margin is at most $\varepsilon/(4+3\varepsilon)$. This conclusion concerns every numerator refit and arbitrary copies, rather than only the displayed witness.

## One common limit and full column rank

The uniform coefficient bound

$$ |A_a(x)|\leq K_m,\qquad K_m=10(m+1)2^m+1 $$

holds for every table in the family and every cube input, by the triangle inequality. For $0\lt\varepsilon\leq5/K_m$, use normalized witnesses

$$ \phi_{a,\varepsilon}(x)=\frac{\varepsilon A_a(x)}{5(\varepsilon+|x|)}. $$

At the zero vertex the value is $-1$. At any other vertex its absolute value is at most $\varepsilon K_m/5\leq1$. Thus its full-cube norm is exactly one. Every witness has the correct strict signs, and as $\varepsilon\to0$ it converges to $-\boldsymbol1_{\lbrace x=0\rbrace}$, independently of $a$.

For the entire affine-numerator space, use the head's values $w_0$ at zero and $w_i$ at the singleton vertices as coordinates. The exact chart is

$$ \phi_\varepsilon(x)=\frac{\varepsilon(1-|x|)w_0+(1+\varepsilon)\sum_i x_iw_i}{\varepsilon+|x|}. $$

The selected zero and singleton rows form the identity matrix for every positive $\varepsilon$. At the limit, retain the zero-row value $w_0$ and use $\sum_i x_iw_i/|x|$ on nonzero inputs. The same submatrix is still the identity. Hence no column-rank loss or ill conditioning of that submatrix accompanies the simultaneous collapse of all these strict tables.

None of the tables is strictly represented in that limiting space. The negative gadget singleton labels force both corresponding coordinates $w_i$ to be negative, while their pair value is their average and cannot be positive. Thus the common limiting point supplies only a weak representative, with all nonzero vertices left undecided.

## A different pole repairs every table

Replace the denominator by $B_1(x)=1+|x|$ and retain the original numerator $A_a$. The new head is still admissible and preserves every sign. The integer numerator has absolute value at least one everywhere, so its smallest signed score is at least $1/(n+1)$. Its full-cube norm is at most $K_m$. Therefore its relative margin is at least

$$ \frac1{(n+1)K_m}. $$

Since $n=2m+2$, the logarithm of this denominator is $O(n)$, giving the claimed $\exp(-O(n))$ bound. This proves that the preceding low margins are properties of a fixed denominator family, not intrinsic obstructions to all representations of the truth tables.

## Consequence for a boundary-counting route

A zero-dimensional limiting *output* can conceal $2^{\Omega(n^2)}$ distinct eventual strict label tables, even when the full feature space has stable column rank and every table has a small-width alternate repair. Thus leading-table support, feature rank, and the number of boundary points alone cannot bound the missing label count.

A successful count must retain the parameters governing the signs on the vanishing coordinates and combine them jointly across heads. The ordinary linear arrangement factor can already pay order $n^2$ when there is one head, since there are $2^n$ input rows. This example does not rule out a count exploiting the smaller ratio of rows to total parameters at exponentially large width. No independent multiplication over heads is justified here.
