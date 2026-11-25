# Quantitative margin at the universal logarithmic upper width

## Statement and status

There are absolute constants $C_0,C_1$ such that every sign table on the $n$-cube, for $n\geq32$, has an original admissible xorformer representation with

$$ H\leq C_0\frac{2^n}{n\log n},\qquad \gamma\geq\exp\left(-C_1n^2\log(n+1)\right). $$

Here $\gamma$ is the full-cube relative margin from the question. One may take $C_0=2323202$ and $C_1=100$ with the deliberately loose estimates below.

This is a **written unconditional upper-bound theorem**, obtained by quantifying an inspected remote construction. It is not a new kernel-checked universal-margin declaration. The abstract rank-weighted gap and mass inequalities are kernel checked in `HeadComplexity/Research/QuantitativeRankGluing.lean`. The remote width theorem and algebraic construction were read at commit `3869e33a97a33419acd08b7627966a63c67e3d37`, branch `origin/ar/027ac8030b43`, particularly:

- `Results/UniversalLogSaving.lean`;
- `Results/AffinePlaneCompiler.lean`, `CauchyGridDecoder.lean`, and `ReverseRankCorrection.lean`;
- `Results/ReverseGridAxisRepair.lean`, `AxisZeroTransfer.lean`, and `AxisZeroFaces.lean`.

No remote module was imported or represented as independently rebuilt in this checkpoint. The original definitions and head resource are unchanged.

The important quantitative change is to assign one scale to each **center Hamming rank**, rather than successively choosing a new scale for every center. There are at most $n+1$ ranks even though the cover has exponentially many centers.

## Quantitative local affine-plane modules

Write $q=2^a$ for the finite-field alphabet used by the remote local compiler, and let $r+s=n$. Its scale selection gives $q\leq n$ for $n\geq32$. The compact Cauchy tokens and poles are

$$ \tau_j=\delta\frac{j+1}{q+1},\qquad p_j=1-\tau_j,\qquad \delta=\frac1{4(n+1)}. $$

Both the token separation and pole separation are at least $d=\delta/(q+1)$. Every pole-token difference lies between $1-2\delta$ and $1$.

To decode any prescribed signs at the $q$ tokens, take the degree at most $q-1$ Lagrange numerator for the positive denominator $\prod_j(p_j-t)$. Its polynomial part is zero. The partial-fraction residues satisfy

$$ |\eta_j|\leq E:=q\left[4(n+1)(q+1)\right]^{2(q-1)}. $$

Indeed, each Lagrange denominator has absolute value at least $d^{q-1}$; the numerator evaluated at a pole has absolute value at most one; and the partial-fraction residue denominator contributes a second factor of at least $d^{q-1}$.

The affine-plane line aggregate contains exactly $q$ positive kernels, each at most two, so its magnitude is at most $2q$. In `ReverseRankCorrection`, the row factor has magnitude at most $E$. The displayed choices satisfy

$$ C\leq(n+1)E,\qquad M\leq4(n+1)^2E,\qquad M+C\leq5(n+1)^2E. $$

Consequently every numerator coefficient in the weak rank grid and its shared affine correction is bounded by $10(n+1)^2q^3E$. All constant numerator terms are zero. The weak denominators have minimum at least $1/2$. The exact weight-two strictification replaces this by a minimum at least $1/(n+1)$, while denominator coefficients remain bounded by two in magnitude and the constant denominator term by three.

The remaining $q^2$ Cauchy correction heads already have minimum denominator at least $3/4$ and numerator coefficients at most $E$. Thus the strict grid uses $2q^2+1$ heads with the preceding common bounds.

The exact axis repair replaces each grid head by three heads, plus three shared row-column correction heads. Replacing negative slopes by a larger negative slope cannot decrease any denominator. Since all constant numerator terms vanish, the axis subtraction introduces no constant normalization term. Each repaired row or column value is at most $(n+1)$ times the corresponding numerator coefficient. Summing these values over the grid heads and applying the explicit three-head row-column formula bounds every final numerator coefficient by

$$ 500(n+1)^5q^5E. $$

There are at most $12q^2$ final heads, each with denominator minimum at least $1/(n+1)$. Therefore both the sum of full-cube head norms and the sum of full-cube numerator norms are bounded by

$$ 6000(n+1)^{14}E\leq B_n:=[10(n+1)]^{30n}. $$

Every local module is exactly the desired sign, with value $+1$ or $-1$, at every product-star grid point, and is exactly zero on both axes. These are the identities proved by the remote local construction, not approximation claims.

## Reversal and localization preserve the norm bound

For a center $c$, replace each local coordinate by $c_i(1-x_i)$ and give every coordinate outside the center a positive denominator slope equal to one. The numerator is exactly the original numerator evaluated at the deletion vector, even outside the center downset. The ambient denominator is the corresponding local denominator plus the number of selected outside coordinates.

Thus the denominator remains positive on the entire cube, every slope is strictly positive, and the full-cube head norm cannot exceed the local full-cube norm. Add a common nonnegative penalty $T$ to every outside-coordinate denominator slope. This again cannot increase a head norm. Off the center downset, the integer penalty count is at least one, so the absolute value of the entire module is at most $B_n/T$. The numerator norm bound is why this last estimate is uniform.

## Rank-weighted assembly

Let $M$ be the number of product-star centers in the downward cover. The remote cover is a subset of the cube, so $M\leq N:=2^n$. Omit empty modules if necessary. Set

$$ C=8NB_n,\qquad \alpha_r=C^{n-r},\qquad T=8NB_nC^n, $$

where $r$ is the total number of ones in the center. Give each module of rank $r$ numerator scale $\alpha_r$, and use the common localization penalty $T$.

Fix a vertex of weight $k$ covered by a product star, and put $r=k+2$. At least one rank $r$ module has signed value exactly one before scaling. For any other module whose downset contains the vertex, the total number of deletions is its center rank minus $k$:

- At rank $r$, either there is one deletion in each block, giving the correct sign, or one block has zero deletions, giving an axis zero.
- At a lower rank, the total number of deletions is at most one, so an axis is zero.
- At a higher rank, the contribution can have either sign, but its scale is at most $\alpha_r/C$ and its absolute module value is at most $B_n$.

The total possible adverse contribution from higher-rank modules is therefore at most $MB_n\alpha_r/C\leq\alpha_r/8$. Every outside-downset contribution, regardless of rank, has magnitude at most $\alpha_{\max}B_n/T$. Their total is at most $1/8$. Consequently the assembled score has signed gap at least

$$ \alpha_r-\frac{\alpha_r}{8}-\frac18\geq\frac12. $$

This is exactly the scope of `QuantitativeRankGluing.rank_weighted_sum_gap`; its tail estimate is `scaled_tail_le`. Since localization does not increase norms, `rank_weighted_mass_le` gives total head mass at most

$$ L:=NB_nC^n. $$

No exponential number of sequential scale choices is present. The exponent $n$ comes only from the number of possible ranks.

## Exceptional faces and the final margin

The product cover excludes two positive coordinate faces, with respectively $\lfloor n/2\rfloor$ and $\lceil n/2\rceil$ free coordinates. This includes the top-weight vertices for which no rank $k+2$ center exists. They must be repaired and are not covered by the preceding gap argument.

Use the exact residual corrections from `AxisZeroFaces`: overwrite the first face by the desired signs, then overwrite the second face. Before atom approximation, each correction is zero off its face; the second also preserves the already repaired first face. The resulting exact score has gap at least $1/2$ everywhere. The first residual has norm at most $1+L$, and the second at most $2+L$.

An arbitrary real function of norm at most $A$ on $m$ Boolean variables has a squarefree expansion with coefficient mass at most $3^mA$. Multiplication by the fixed positive face preserves each monomial's one-head approximability. These monomial approximants may be chosen with zero bias, so their head mass also bounds their entire score amplitude. Approximate the combined corrections uniformly to total error at most $1/4$, increasing their total head norm by at most $1/4$. This costs exactly the same $2^{\lfloor n/2\rfloor}+2^{\lceil n/2\rceil}$ heads as the remote proof. The final score has gap at least $1/4$ and total head mass at most $10\cdot3^n(L+1)$. Hence

$$ \gamma\geq\frac1{40\cdot3^n(L+1)}. $$

For $n\geq32$, $\log B_n\leq60n\log(n+1)$, whence $\log L\leq63n^2\log(n+1)$. The last display therefore implies the asserted conservative bound with $C_1=100$. Every head is admissible on the entire original cube, including the exceptional-face approximants.

The head count is unchanged from the remote construction. Its explicit width estimate supplies $C_0=2323202$.

## What this does and does not settle

The exceptional-table class is empty once the comparison width reaches this universal logarithmic upper width and the required margin is at most the bound above. This quantitatively narrows the possible obstruction to sparse repair.

It does not improve the unrestricted lower bound. At the benchmark width $H=cN/n^{3/2}$, the universal compiler has overhead of order $\sqrt n/\log n$, with coefficient proportional to $1/c$. Thus taking $c$ smaller does not make its comparison class smaller; the universal width remains fixed. It cannot be inserted into the small-constant high-margin counting theorem to obtain a contradiction.

A localized version would be useful only with an additional theorem showing that an original narrow score needs this expensive compiler on sufficiently few jointly treatable regions. Arbitrary active constraints or individual bad representations do not supply that access statement.

An independent agent audited the local Cauchy, rank-correction, strictification, axis-repair, localization, rank-assembly, and exceptional-face estimates against the cited remote source. The local row-column numerator estimate admits the smaller constant $120$ in place of $500$, leaving slack in the stated bound. The three abstract numerical declarations build successfully and their transitive axiom output is exactly `[propext, Classical.choice, Quot.sound]`.
