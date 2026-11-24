# A linear-width product compiler for one affine pencil

## Statement and scope

Let $H\geq1$. Suppose a strict score on the full Boolean cube has the form

$$ S(x)=\sum_{h=1}^H\frac{A_h(x)}{\alpha_h+\beta_h L(x)},\qquad \alpha_h+\beta_h L(x)\gt0, $$

where $A_h$ and $L$ are arbitrary real affine functions. Then its entire truth table is represented by $H$ affine-product terms

$$ T(x)=\sum_{j=0}^{H-1}C_j(x)\prod_{i:x_i=1}z_{ji}. $$

The $C_j$ are affine and the factors $z_{ji}$ may all be positive. There is no coefficient bound, separation assumption on the poles, or relative-margin hypothesis. An arbitrary original bias can be absorbed into one numerator. The same result therefore holds for every actual original admissible certificate whose full denominators lie in one affine pencil.

The replacement terms belong to the comparison class in [the affine-product count](affine_product_capacity.md). They are not claimed to be original heads. This theorem is a margin-free compiler for a restricted denominator family, not an unrestricted margin repair or a new lower bound for $W(n)$.

## Proof

Set $B_h(z)=\alpha_h+\beta_h z$. Positive global clearing gives

$$ P(x)=\sum_{h=1}^H A_h(x)\prod_{g\neq h}B_g(L(x))=\left(\prod_{h=1}^H B_h(L(x))\right)S(x). $$

For each affine coefficient separately, the cleared polynomial has degree at most $H-1$ in the single statistic. Thus there are affine functions $Q_r$ such that

$$ P(x)=\sum_{r=0}^{H-1}Q_r(x)L(x)^r. $$

For $t\gt0$, define

$$ V_t(x)=\frac{\exp(tL(x))-1}{t},\qquad P_t(x)=\sum_{r=0}^{H-1}Q_r(x)V_t(x)^r. $$

For every vertex, $V_t(x)\to L(x)$ and $P_t(x)\to P(x)$ as $t\to0^+$. The cube is finite and $P$ is strict, so one sufficiently small positive $t$ preserves every sign simultaneously. Expanding each power of $\exp(tL)-1$ and grouping equal powers of the same exponential yields

$$ P_t(x)=\sum_{j=0}^{H-1}C_{j,t}(x)\exp(jtL(x)). $$

Each $C_{j,t}$ is affine. Writing $L(x)=l_0+\sum_i l_i x_i$ gives

$$ C_{j,t}(x)\exp(jtL(x))=\left(\exp(jt l_0)C_{j,t}(x)\right)\prod_{i:x_i=1}\exp(jt l_i). $$

This has exactly the required form. No lower bound on the original margin was used. $\blacksquare$

## Relation to the obstructions

The [approximate shared-direction obstruction](approximate_shared_direction_obstruction.md) allows every replacement reciprocal pole in the original pencil and proves a very small margin for all such replacements that agree on more than $15/16$ of the cube. The compiler here changes the comparison family and is consistent with that obstruction. In particular, pole conditioning inside the original pencil and product sign complexity are different quantities.

For several independent pencils, clearing each group separately does not give a valid compiler for their sum: the groups are multiplied by different positive functions, which can alter their signed cancellation. Clearing every group with one common multiplier restores the truth table but introduces products across the groups. The single-statistic regrouping above no longer bounds the term count by the sum of the group widths.

More generally, for strict scores $S$ and $T$ on a finite cube, they have the same truth table if and only if there is a positive function $M$ on the cube with $T(x)=M(x)S(x)$. Thus an unrestricted sign compiler may choose a different positive multiplier for every score. The known border-rank obstruction for the specific multiplier $\prod_h B_h$ does not exclude that freedom. No useful uniform bound for this wider multiplier problem is proved here.

## A failed stability shortcut

Positive affine factors are real stable, but their Boolean multilinear reduction need not remain real stable. An exact counterexample is

$$ B_1=1+x+8y+8z,\qquad B_2=2+10x+9y+z. $$

Reducing $B_1B_2$ with $x^2=x$, $y^2=y$, and $z^2=z$ gives

$$ Q=2+22x+97y+25z+89xy+81xz+80yz. $$

Its Rayleigh difference is

$$ (\partial_x Q)(\partial_y Q)-Q\partial_x\partial_y Q=1956+7392z+6480z^2. $$

At $z=-77/135$ this is $-6844/45$. To check nonstability directly, specialize $z$ to that real value and write the resulting bivariate polynomial as $a x y+b x+c y+d$. For $x$ in the upper half-plane its zero $y=-(b x+d)/(a x+c)$ has imaginary part $(ad-bc)\mathrm{Im}(x)/|a x+c|^2\gt0$. Choosing $x=\mathrm{i}$ and perturbing $z$ a sufficiently small distance into the upper half-plane preserves this strict inequality by continuity, producing a zero with all three coordinates in the upper half-plane. This rules out transferring ordinary denominator-product stability through the Boolean quotient. It makes no claim about the unrestricted multiplier problem.

## Kernel verification

The module is `formalization/HeadComplexity/Research/PencilProductCompiler.lean`. Its principal declarations are:

- `HeadComplexity.PencilProductCompiler.mem_represented_of_affine_polynomial`, the finite-difference compiler before clearing.

- `HeadComplexity.PencilProductCompiler.mem_represented_of_pencil`, the positive one-pencil rational compiler.

- `HeadComplexity.PencilProductCompiler.mem_represented_of_original_pencil`, the bridge from actual `FracAtom` denominators and an arbitrary original bias.

`lake build HeadComplexity.Research.PencilProductCompiler` passed with 4030 jobs. The public audit and the all-declaration transitive audit report only `propext`, `Classical.choice`, and `Quot.sound`. The stability counterexample and its interpretation are written proofs, not Lean declarations. No original definition was changed.
