# High-order mixed-point amplitude obstruction

## Statement and status

This is a written unconditional theorem for the original coherent-denominator head model, allowing arbitrary width, real coefficients, signed cancellation, and bias. It uses the exact positive scalar-feature expansion in `margin_repair_anchored_atomic_decomposition.md`. The underlying positive reciprocal expansion and the coefficient-mass inequality are now kernel checked in `PositiveReciprocalExpansion` and `AnchoredAtomicDecomposition`; this high-order functional argument is not yet formalized.

Fix a Boolean vertex $v$ with $r$ one-coordinates and $s$ zero-coordinates, where $r+s=n$. Let $1\leq k\leq\min(r,s)$. Suppose an original score $S=b+\sum_h\phi_h$ uniformly approximates its point indicator with error at most $\epsilon$. Then its full-cube amplitude satisfies

$$ |b|+\sum_h\|\phi_h\|_\infty\geq\frac{1-4^k\epsilon}{2n+1}\min\left\lbrace\binom rk,\binom sk\right\rbrace. $$

The bound is meaningful when $4^k\epsilon\lt1$. In particular, for a balanced mixed vertex and arbitrarily accurate value approximation, every bound on the total amplitude must be at least exponential in $n$. The number of heads does not affect this conclusion.

This concerns approximation of a real-valued gate. It is not a lower bound for representing the point-indicator truth table, which is an affine threshold with a healthy original-head representation.

## The averaged mixed-difference functional

Let $P$ be the one-coordinates of $v$ and $Q$ its zero-coordinates. For $A\subseteq P$ and $B\subseteq Q$, write $v-A+B$ for the vertex obtained by changing the coordinates in $A$ to zero and those in $B$ to one. Define

$$ L_k F=\frac1{\binom rk\binom sk}\sum_{\substack{D\subseteq P,\ |D|=k\cr U\subseteq Q,\ |U|=k}}\sum_{A\subseteq D}\sum_{B\subseteq U}(-1)^{|A|+|B|}F(v-A+B). $$

For each pair $(D,U)$, the inner sum has $4^k$ coefficients of absolute value one. Consequently $|L_kF|\leq4^k\|F\|_\infty$. Every constant is annihilated because $k\geq1$, while the point indicator has $L_k\mathbf1_v=1$. Therefore

$$ |L_k S|\geq1-4^k\epsilon. $$

The exact operator norm is also $4^k$: repeated occurrences of the same vertex have the same sign, determined by its distance from $v$. The upper bound alone is sufficient here.

## Action on the scalar dictionary

A positive-orientation head has an exact expansion into scalar features of the forms

$$ F_S(x)=\prod_{j\in S}(1-x_j),\qquad G_{i,S}(x)=x_i\prod_{j\in S}(1-x_j),\qquad i\notin S, $$

with total absolute coefficient mass at most $(2n+1)\|\phi\|_\infty$. This is the full-cube coefficient bound in the cited decomposition note. It permits arbitrary signed affine numerators. Constant-denominator heads satisfy the same estimate by their affine expansion.

For either scalar feature,

$$ |L_kF_S|\leq\binom rk^{-1},\qquad |L_kG_{i,S}|\leq\binom rk^{-1}. $$

**Proof.** Put $y_i=1-x_i$ on $P$ and $z_j=x_j$ on $Q$, so $v$ corresponds to $y=z=0$. An alternating difference in a selected coordinate set extracts, up to a global sign, the coefficient of that squarefree monomial after all unselected coordinates are set to zero.

The $P$-factor of $F_S$ is the single monomial $y_{S\cap P}$. Thus its $k$-fold difference is nonzero for at most one choice of the $k$-set $D$.

If $i\in P$, the $P$-factor of $G_{i,S}$ is

$$ y_{S\cap P}-y_{(S\cap P)\cup\lbrace i\rbrace}. $$

The two monomials have different degrees. For a fixed $k$, at most one can contribute, and again at most one selected $D$ gives a nonzero difference. If $i\in Q$, the $P$-factor is still the single monomial $y_{S\cap P}$.

In every case the $Q$-factor is a product of negative literals, possibly multiplied by one positive literal. Every squarefree coefficient of this factor has absolute value at most one. Averaging its differences over all $k$-sets $U$ therefore gives absolute value at most one. Averaging over the $\binom rk$ choices of $D$ proves the claim. No bound by $2^k$ is needed for this second average.

Applying the scalar coefficient-mass estimate gives

$$ |L_k\phi|\leq\frac{2n+1}{\binom rk}\|\phi\|_\infty $$

for every positive-orientation head. Simultaneously complementing every coordinate swaps $P$ and $Q$ and changes at most a common sign in the alternating differences. Hence every negative-orientation head satisfies

$$ |L_k\phi|\leq\frac{2n+1}{\binom sk}\|\phi\|_\infty. $$

The bias is annihilated. Summing these bounds and combining with $|L_kS|\geq1-4^k\epsilon$ proves the stated theorem.

## Product-compiler consequence and limits

Let $r=s=m$, so $n=2m$, and choose $k=\lfloor m/2\rfloor\geq1$. The point indicator is the product of the two opposite anchored-face indicators

$$ \mathbf1_v=\left(\prod_{i\in P}x_i\right)\left(\prod_{j\in Q}(1-x_j)\right). $$

Each factor is uniformly approximable by one genuine head with bounded full-cube norm. Nevertheless, any arbitrarily accurate original-head approximation to their product must have total amplitude at least

$$ \frac{\binom m{\lfloor m/2\rfloor}}{4m+1}\geq\frac{2^m}{(m+1)(4m+1)}. $$

More precisely, the same conclusion multiplied by $1/2$ already holds for error $\epsilon\leq1/(2\cdot4^k)$. Thus no product compiler can preserve a polynomial amplitude bound uniformly in the approximation tolerance, even if its output width is unlimited. This rules out a value-compilation argument that silently treats multiplication of bounded coherent heads as having only polynomial norm cost.

Exponential amplitude in $n$ is still compatible with relative margin $\exp(-\mathrm{poly}(n))$. The theorem therefore does not obstruct the benchmark margin repair, a sign-only compiler, a compiler with exponential amplitude, or the approximate-truth-table counting interface. The earlier first-order mixed-star argument gives a stronger constant-error estimate, of order $\min(r,s)$, without the $4^k$ accuracy requirement.

## Independent audit

A second agent checked the exact-support condition for the downward difference, the two consecutive degrees contributed by one positive literal, the absence of an extra $2^k$ factor in the upward average, the complement symmetry, and the $4^k$ approximation-error factor. The proof passed that audit. The entire statement remains a written theorem; no new Lean declaration is claimed in this note.
