# An Explicit Pure RoPE Boolean Separation

## Statement

There is an explicit finite Boolean function for which replacing additive positions by pure rotary query/key encoding strictly reduces the number of heads. The construction below uses

$$ m=2^{400000},\qquad n=14m. $$

Its exact pure complexity is three, its threshold degree is three, and its vanilla complexity is either four or five:

$$ \deg_{\pm}(f)=H_P(f)=3\lt4\leq H_V(f)\leq5. $$

The function is not invariant under complementing every input bit. The vanilla lower bound allows all parameters, all finite widths, and arbitrary differences between positions within the groups used in the construction. It concerns Boolean signs, not equality of scores.

The strict inequality between `PureRoPEHStar` and the original vanilla `HStar` is **Lean-certified**, including the lower bound against every vanilla representation. Exact rational certificates independently verify the numerical constants. The realization of pure atoms by literal rotary matrices uses the mathematical bridge in Theorem 14. The model definitions are unchanged.

## The function and its pure atoms

Index the bits by $(i,r)$, where $1\leq i\leq14$ and $1\leq r\leq m$. Define their group means and six rational linear forms by

$$ z_i(x)=\frac1m\sum_{r=1}^m(2x_{i,r}-1),\qquad S_h(z)=\sum_{i=1}^{14}s_{h,i}z_i,\qquad B_h(z)=\sum_{i=1}^{14}b_{h,i}z_i, $$

$$ s_{h,i}=\frac{i^h}{10000},\qquad b_{h,i}=\frac{i^{h+3}-(15/2)^{h+3}}{10^9},\qquad h\in\lbrace0,1,2\rbrace. $$

Put $D_h=1+B_h$ and define

$$ F(z)=S_0D_1D_2+S_1D_0D_2+S_2D_0D_1,\qquad f(x)=\mathbf{1}[F(z(x))\gt0]. $$

This is the promised explicit Boolean formula. Its input length and every coefficient are specified; no search, choice of a favorable truth table, or unknown replication count occurs in the definition.

For a strict three-head implementation, put

$$ W=32\cdot10^9,\qquad A=10000W^2,\qquad \varepsilon=\frac{1}{16Am^3}. $$

An equivalent formula uses integers only. Set

$$ r_i=\sum_{r=1}^m(2x_{i,r}-1),\qquad I_h=\sum_{i=1}^{14}i^h r_i,\qquad J_h=\sum_{i=1}^{14}\left(32i^{h+3}-2^{2-h}15^{h+3}\right)r_i,\qquad E_h=Wm+J_h. $$

Then

$$ f(x)=\mathbf{1}[I_0E_1E_2+I_1E_0E_2+I_2E_0E_1\gt0]. $$

For head $h$ and position $(i,r)$, use the following pure scalar parameters:

$$ a_{h,i,r}=\frac{s_{h,i}-b_{h,i}}m,\qquad \widehat b_{h,i,r}=\frac{s_{h,i}+b_{h,i}}m,\qquad \gamma_h=1-\sum_{i=1}^{14}s_{h,i}, $$

$$ \eta_h=-\sum_{i=1}^{14}b_{h,i},\qquad v_{0,h}=-1,\qquad v_{1,h}=1,\qquad c=-\varepsilon. $$

Here $c$ is the final readout constant, not an extra head. All these parameters are rational. Exact arithmetic verifies

$$ s_{h,i}\gt|b_{h,i}|,\qquad \sum_i s_{h,i}\lt1,\qquad \sum_i|b_{h,i}|\lt\frac12. $$

The atom denominator is $D_h(z(x))$, and its numerator is $S_h(z(x))$. Consequently the complete score is

$$ T(x)=-\varepsilon+\sum_{h=0}^2\frac{S_h(z(x))}{D_h(z(x))}=-\varepsilon+\frac{F(z(x))}{D_0(z(x))D_1(z(x))D_2(z(x))}. $$

### Theorem 1. Exact verification on the entire Boolean cube

Every denominator is positive and their product is less than eight. Each $Wb_{h,i}$ and $10000s_{h,i}$ is an integer. Since each $mz_i(x)$ is an integer,

$$ Am^3F(z(x))\in\mathbb Z. $$

Therefore a nonzero value of $F$ has magnitude at least $1/(Am^3)$, and the unshifted score has magnitude greater than $1/(8Am^3)=2\varepsilon$. Subtracting $\varepsilon$ preserves every nonzero sign and sends every zero to $-\varepsilon$. Thus, for every one of the $2^n$ inputs,

$$ T(x)\gt0\Longleftrightarrow f(x)=1,\qquad |T(x)|\geq\varepsilon. $$

This is a symbolic full-cube sign verification, including ties; it does not rely on enumerating the cube. At the all-one input every $S_h$ is positive, while at the all-zero input every $S_h$ is negative. Hence these complementary inputs have different labels.

The integer identity, strict sign equivalence, margin, actual unshifted function's pure upper bound, and failure of global complement invariance are Lean-checked in [PureRoPEReplicationStrict.lean](../../formalization/HeadComplexity/Results/PureRoPEReplicationStrict.lean). The relevant declarations are `scaled_cubic_integer`, `full_cube_strict`, `explicitUnshiftedFunction_pure_three`, `explicitUnshiftedFunction_margin`, and `explicitUnshiftedFunction_not_complement_invariant`.

### Theorem 2. Realization in the specified architecture

The parameters above are pure atoms with token-only values. The fixed-query, fixed-frequency interpolation theorem in [Theorem 14](014_rope_head_complexity.md) realizes any finite list of their positive weights: interpolate the logits $\log a_{h,i,r}$ and $\log\widehat b_{h,i,r}$ with standard rotary features, set the query self-logit to $\log\gamma_h$, and set its value to $\eta_h/\gamma_h$. Shared independent embeddings for tokens $0,1,=$ and an output direction realize all three heads simultaneously. The output constant is $-\varepsilon$.

An even head dimension at least $n$ suffices for the interpolation. It is finite, although enormous. Values are never rotated and no additive positional embeddings are used. The usual normalization of dot-product logits is absorbed into the key maps. Thus the construction is valid in the literal architecture from the question, with either the standard frequency schedule or free frequencies.

## A quantitative obstruction for all vanilla cubic tensors

Write $F_3$ for the homogeneous cubic part of $F$:

$$ F_3=S_0B_1B_2+S_1B_0B_2+S_2B_0B_1. $$

The [quantitative cubic appendix](../../artifacts/rope/quantitative_cubic_gap/README.md) proves the following uniform statement. If

$$ R=N_0E_1E_2+N_1E_0E_2+N_2E_0E_1 $$

is a homogeneous cubic in fourteen variables, each $N_h$ is arbitrary, and each $E_h$ has strictly positive coefficients, strictly negative coefficients, or is zero, then some squarefree cubic coefficient of $R-F_3$ has magnitude greater than $2^{-2000}$. In particular, no sequence of such tensors converges coefficientwise to $F_3$.

For clarity, the mechanism is summarized here. The six forms $S_h,B_h$ are independent, and every six-row minor of their coefficient matrix is nonzero. Every $B_h$ has both signs. On the kernel of a nonnegative denominator direction, one can choose a bounded point where the target cubic's Hessian has a six-by-six minor with determinant bounded away from zero. The competing vanilla cubic has Hessian rank at most five at that point, because one of its denominator forms vanishes. A finite determinant perturbation estimate gives a uniform gap for the complete cubic coefficients. Finally, a cubic depending on at most six linear forms has Hessian rank at most six. Invertible disjoint cross blocks of the target Hessians recover every repeated-index coefficient continuously from its squarefree coefficients, with explicit bounds. This gives the stated squarefree gap, including unbounded numerators, colliding denominators, zero directions, and arbitrary untied competitors.

The rational constants and every numerical inequality in this argument are checked by [verify_gap.py](../../artifacts/rope/quantitative_cubic_gap/verify_gap.py). The mass bounds, all 3003 six-row minors, and all 182 required cross-Hessian minors are independently checked by [verify.py](../../artifacts/rope/generic_cubic_completion/verify.py).

## Forcing a sign polynomial close to the target

We next convert this coefficient obstruction into a Boolean obstruction. All coefficient norms below are maximum norms in the ordinary monomial basis, with no factorial normalization.

### Theorem 3. A finite rational zero-surface certificate

Let $M$ be the invertible linear coordinate map

$$ Mz=(S_0(z),S_1(z),S_2(z),B_0(z),B_1(z),B_2(z),z_7,\ldots,z_{14}). $$

Its inverse has maximum absolute row sum less than $2^{34}$, and every entry of $48M^{-1}$ is an integer. Write its coordinates as $(u_0,u_1,u_2,v_0,v_1,v_2,w_1,\ldots,w_8)$. On the zero set of $F$, solve for the first coordinate:

$$ u_0=-\frac{u_1(1+v_0)}{1+v_1}-\frac{u_2(1+v_0)}{1+v_2}. $$

Let $L=10\cdot2^{40}$, and let each of the thirteen free coordinates range independently over

$$ \lbrace0,1,\ldots,9\rbrace/L. $$

This defines a finite set $\mathcal Z$ of rational zeros of $F$. Each lies in the cube of coordinate radius $1/16$. Each point has a common coordinate denominator less than $2^{138}$: one may use

$$ 48L(L+j_1)(L+j_2),\qquad 0\leq j_1,j_2\leq9, $$

where $v_1=j_1/L$ and $v_2=j_2/L$.

The vector space of polynomials in fourteen variables of total degree at most three has dimension $680$. Evaluation on $\mathcal Z$ has kernel exactly the one-dimensional span of $F$.

**Proof.** After the displayed substitution for $u_0$, multiply a polynomial of degree at most three by $((1+v_1)(1+v_2))^3$. The result is a polynomial in thirteen variables of total degree at most nine. If it vanishes at the ten-point product grid, repeated univariate interpolation makes it identically zero.

The polynomial $F$ is irreducible. In these coordinates it is linear in $u_0,u_1,u_2$, and their three coefficient polynomials have greatest common divisor one. It is therefore primitive and irreducible over the polynomial ring in the remaining coordinates, by the linear-polynomial case of Gauss's lemma. Vanishing on the rational graph implies divisibility by $F$, first over the field of rational functions in the other variables and then in the polynomial ring. Since both degrees are at most three and $F$ has degree three, the quotient is constant. $\blacksquare$

Choose an index $j$ of a nonzero coefficient $F_j$. Removing column $j$ from the evaluation matrix leaves $679$ independent columns, so some $679$ rows form a nonsingular square matrix. Every matrix entry has magnitude at most one. Clearing the denominator of each row requires a factor less than $2^{414}$. The determinant consequently has magnitude greater than $2^{-414\cdot679}$. The cofactor formula bounds the maximum absolute row sum of the inverse by

$$ 679!\cdot2^{414\cdot679}\lt2^{300000}. $$

In this display the product is ordinary multiplication. The bound follows directly from $679!\leq1024^{679}$. No choice of the minor needs to be computed: every nonzero minor obeys this bound, and the interpolation argument proves that one exists.

The exact map, denominator bounds, coefficient bounds, and polynomial identities are checked in [verify_chart.py](../../artifacts/rope/generic_cubic_completion/verify_chart.py). Its additional finite-field rank check is corroborating evidence; the interpolation proof supplies the full-grid rank statement used here.

The displayed rational inverse, its denominator and row bounds are also Lean-checked in `PureCubicChart.lean`. The ten-point product-grid interpolation step is `PureCubicGraph.eq_zero_of_chartGrid`. Graph divisibility, the exact finite kernel, bounded integer row denominators, and evaluation-minor recovery are all checked in `PureCubicRawKernel.lean`, `PureCubicNodeBounds.lean`, and `PureCubicInterpolation.lean`.

### Theorem 4. Quantitative sign rigidity on the mean grid

Let $Q$ be any polynomial of total degree at most three that has the same Boolean classifier as $F$ on the grid

$$ G_m=\lbrace-1,-1+2/m,\ldots,1\rbrace^{14}. $$

It is enough that $Q$ be positive wherever $F$ is positive and nonpositive wherever $F$ is nonpositive. Normalize $Q$ by a positive scalar so that its largest coefficient magnitude is one. This is possible because $F$ is positive at the all-one point.

There is a positive scalar $c$ such that

$$ \|Q-cF\|_{\mathrm{coef},\infty}\lt e,\qquad e=2^{300067}/m=2^{-99933},\qquad c\geq\frac12. $$

**Proof.** A degree-three polynomial with coefficient norm at most one has Lipschitz constant at most $3\cdot680=2040$ on the unit cube, for coordinate maximum distance. This follows by bounding each monomial derivative and summing its degree. The same bound applies to $F$, whose coefficient norm is less than one.

Fix $a\in\mathcal Z$, and put $v=M^{-1}e_0$, where $e_0$ selects the $u_0$ coordinate. Set $t=2^{20}/m$. The points $a\pm tv$ are inside the unit cube, and

$$ F(a\pm tv)=\pm t(1+B_1(a))(1+B_2(a)). $$

The two factors have product at least $1/4$. Round each point to a nearest point of $G_m$, at coordinate distance at most $1/m$. The rounding changes $F$ by at most $2040/m$, which is less than $t/4$. Thus the two rounded points have opposite strict signs of $F$. They have the corresponding weak or strict signs of $Q$ and are each at distance less than $2^{55}/m$ from $a$. The Lipschitz estimate gives

$$ |Q(a)|\lt2^{67}/m. $$

Choose $j$ with $F_j\neq0$, and set $c=Q_j/F_j$. The polynomial $Q-cF$ has coefficient $j$ equal to zero and has the same evaluations as $Q$ on $\mathcal Z$. Applying the inverse bound from Theorem 3 gives the stated coefficient error $e$.

It remains to check the sign and size of $c$. Since $\|F\| _{\mathrm{coef},\infty}\leq1$ and $\|Q\| _{\mathrm{coef},\infty}=1$, we have $|c|\geq1-e\gt1/2$. Moreover, $F(\mathbf1)\gt10^{-4}$, while the error polynomial has value of magnitude at most $680e$ at $\mathbf1$. If $c$ were negative, $Q(\mathbf1)$ would be negative because $e\lt2^{-30}$, contradicting its required positive sign. Hence $c\gt0$. $\blacksquare$

## Excluding every vanilla representation

### Theorem 5. Untied vanilla parameters survive averaging

Suppose a three-head vanilla model computes $f$. Its exact affine-fraction normal form gives a degree-at-most-three sign polynomial $P$ on the $14m$ centered bit variables, obtained by clearing its positive denominators. Its homogeneous cubic part has the form

$$ N_0E_1E_2+N_1E_0E_2+N_2E_0E_1. $$

The numerator directions are arbitrary. Every denominator direction has all positive coefficients, all negative coefficients, or all zero coefficients. Absorb the readout constant into one numerator. These statements follow from the original vanilla normal form and impose no additional restrictions on the representation.

Multilinearize $P$ on the spin cube and average it over all permutations within each group of $m$ positions. The average has the same classifier, since $f$ depends only on the group means. Express this symmetric multilinear polynomial as a polynomial $Q(z)$ in the fourteen means. Its total degree is at most three. For example, averaging a product of two or three distinct spins within one group gives respectively

$$ \frac{mz_i^2-1}{m-1},\qquad \frac{m^2z_i^3-(3m-2)z_i}{(m-1)(m-2)}. $$

These formulas follow by expanding powers of the sum of the spins and using that each spin has square one. Thus $Q$ has exactly the required classifier on $G_m$.

Crucially, the coefficient of $z_i z_j z_k$ for three distinct groups is the sum of the original cubic coefficients on one coordinate from each of these groups. It is exactly the corresponding coefficient of

$$ R=\overline N_0\overline E_1\overline E_2+\overline N_1\overline E_0\overline E_2+\overline N_2\overline E_0\overline E_1, $$

where a bar replaces each linear coefficient by its sum over the positions in that group. No finite-population correction occurs for three distinct groups. Terms with repeated groups cannot contribute to a monomial using three distinct groups. Each $\overline E_h$ still has uniformly positive coefficients, uniformly negative coefficients, or is zero. Therefore the squarefree cubic tensor of $Q$ belongs to the full vanilla class excluded above, even though its repeated-index cubic coefficients need not belong to that class.

This argument is why averaging does not impose a tied-parameter assumption on the competitor. The [replication appendix](../../artifacts/rope/generic_cubic_completion/replication.md) supplies further details.

### Theorem 6. The strict separation

Apply Theorem 4 to the positively normalized averaged polynomial $Q$. Dividing by the resulting positive $c$ produces a squarefree cubic tensor in the same vanilla class, at coefficient distance less than

$$ 2e=2^{-99932}\lt2^{-2000} $$

from $F_3$. This contradicts the quantitative exclusion radius. Hence no vanilla model with three heads computes $f$. A representation with fewer heads could be padded with zero-output heads, so $H_V(f)\geq4$.

The explicit pure construction gives $H_P(f)\leq3$. [Theorem 16](016_pure_rope_two_head_equality.md) shows that every function computable with at most two pure heads is computable with at most two vanilla heads. Thus $H_P(f)=3$.

The threshold degree is also exactly three. The strict polynomial

$$ F-\varepsilon D_0D_1D_2 $$

has degree at most three and realizes $f$. Conversely, apply Theorem 4 to a hypothetical degree-at-most-two sign polynomial, averaged over groups as above. Its cubic coefficients vanish. Some cubic coefficient of $F$ is nonzero, because its six defining forms are independent, and every coefficient of $F$ has denominator dividing $A\lt2^{84}$. Its magnitude is therefore greater than $2^{-84}$. The estimate $c\geq1/2$ contradicts the coefficient error $e\lt2^{-85}$. This proves $\deg_{\pm}(f)=3$.

### Theorem 7. An explicit five-head vanilla upper bound

Write the strict polynomial as

$$ G=U_0D_1D_2+U_1D_0D_2+U_2D_0D_1,\qquad U_0=S_0-\varepsilon D_0,\quad U_1=S_1,\quad U_2=S_2. $$

The additional affine form $E=10D_0-D_1$ is positive throughout the cube, since $D_0\gt1/2$ and $D_1\lt2$ give $E\gt3$. Its coefficient on mean variable $z_i$ is

$$ e_i=10b_{0,i}-b_{1,i}=-\frac{i^4-10i^3+16875/16}{10^9}\leq-\frac{411}{16\cdot10^9}\lt0. $$

The inequality is an exact check at the fourteen integer indices, with equality at $i=7$. Thus $E$ has strictly negative slopes in the original bit variables. Substituting $D_1=10D_0-E$ gives

$$ G=10U_2D_0^2+(10U_0+U_1)D_0D_2-E(U_2D_0+U_0D_2). $$

Set $a=\varepsilon/2^{40}$. For affine forms $u,v$, put

$$ \Delta_{uv}=\frac1E-\frac1{E+au}-\frac1{E+av}+\frac1{E+a(u+v)},\qquad \delta_u=\frac1E-\frac1{E+au}. $$

The score

$$ V_a=10U_2\Delta_{D_0D_0}+(10U_0+U_1)\Delta_{D_0D_2}-2aU_2\delta_{D_0}-2aU_0\delta_{D_2} $$

uses only five denominators. Its exact affine numerators are as follows.

| Denominator | Numerator |
| --- | --- |
| $E$ | $(10-2a)U_0+U_1+(10-2a)U_2$ |
| $E+aD_0$ | $-10U_0-U_1+(-20+2a)U_2$ |
| $E+2aD_0$ | $10U_2$ |
| $E+aD_2$ | $(-10+2a)U_0-U_1$ |
| $E+a(D_0+D_2)$ | $10U_0+U_1$ |

Every denominator is positive. In mean coordinates each denominator slope differs from $e_i$ by less than $2a$, because $|b_{h,i}|\lt1$. Also $\varepsilon\lt1/16$, so

$$ 2a\lt2^{-43}\lt\frac{411}{16\cdot10^9}. $$

All five denominators consequently have strictly negative slopes. Their numerators are arbitrary affine forms, so all five fractions are admissible in the unchanged vanilla model.

For $0\lt u,v\lt2$, elementary reciprocal difference estimates give

$$ \left|\frac{\Delta_{uv}}{a^2}-\frac{2uv}{E^3}\right|\leq\frac{96a}{E^4},\qquad \left|\frac{\delta_u}{a}-\frac{u}{E^2}\right|\leq\frac{8a}{E^3}. $$

For the first estimate, integrate $2uv/(E+su+tv)^3$ over the square $0\leq s,t\leq a$ and compare with its value at zero. For the second, integrate $u/(E+su)^2$ over $0\leq s\leq a$. All intermediate denominators are at least $E$. Using $|U_h|\lt2$ and $E\gt3$, these bounds imply

$$ \left|\frac{V_a}{a^2}-\frac{2G}{E^3}\right|\leq\frac{4032a}{E^4}+\frac{64a}{E^3}\leq\frac{4096a}{E^3}\lt\frac{\varepsilon}{4E^3}. $$

The pure score margin gives $|G|\gt\varepsilon/8$, hence $|2G/E^3|\gt\varepsilon/(4E^3)$. Therefore $V_a$ has the sign of $G$ at every Boolean input, including every original zero of $F$. This proves $H_V(f)\leq5$ with an explicit rational construction. The [five-head certificate](../../artifacts/rope/five_head_upper/README.md) checks the identities and constants; [construction.json](../../artifacts/rope/explicit_separation/construction.json) contains all five affine fractions. $\blacksquare$

The earlier general seven-head compiler remains Lean-checked as `vanilla_seven_of_pureRoPE_three`. Its certificate is retained for comparison; the five-head improvement uses the additional oriented relation special to this target.

## Certification scope

The explicit atom parameters, all-input sign identity and margin, finite interpolation argument, untied vanilla lower bound, and scalar-to-architecture bridge together prove the stated Boolean separation. No fitting failure or restricted-family infeasibility is used as a lower bound.

The complete scalar/original-vanilla Boolean separation is Lean-certified in [PureRoPEExplicitSeparation.lean](../../formalization/HeadComplexity/Results/PureRoPEExplicitSeparation.lean). The declarations `not_vanilla_three`, `vanillaHStar_ge_four`, `pureHStar_eq_three`, `strict_separation`, `shared_strict_separation`, and `not_universal_equality` have no unproved hypotheses. They include arbitrary real parameters, untied replicas, constant heads, and zero scores on false inputs. The exact threshold degree is checked by `PureRoPEExplicitThreshold.thresholdDeg_eq_three` in [PureRoPEExplicitThreshold.lean](../../formalization/HeadComplexity/Results/PureRoPEExplicitThreshold.lean), quantifying over every real threshold polynomial.

The exact atom parameters, integer-cubic identity, rational tie removal, full-cube margin, and non-complement-invariance are also Lean-certified. The literal rotary-matrix realization remains a mathematical proof in Theorem 14. The five-head upper bound is Lean-certified by `PureRoPEReplicationFive.explicit_sharedHStar_le_five` in [PureRoPEReplicationFive.lean](../../formalization/HeadComplexity/Results/PureRoPEReplicationFive.lean). For the particular rational step $a=\varepsilon/2^{40}$, denominator admissibility is Lean-certified by `PureCubicFiveDenominators.fraction_admissible` in [PureCubicFiveDenominators.lean](../../formalization/HeadComplexity/Polynomial/PureCubicFiveDenominators.lean); its finite-difference sign estimate is the mathematical proof above.

Further supporting Lean results include the following:

- `pureRoPEComputable_two_iff_vanilla` and `pureRoPEHStar_eq_vanilla_of_le_two` exclude the requested two-versus-three route universally.

- `MeanGridCubic.cubic_mean_sign_exists` proves that averaging arbitrary untied cubic parameters gives a degree-at-most-three mean polynomial with the same strict-positive and weak-negative labels. `CubeTopCoefficients.meanPolynomial_cubic_coefficient` proves that its coefficients on three distinct groups equal the raw group-summed coefficients. `ThreeHeadReplication.coefficient_sum_three_groups` and `ThreeHeadReplication.uniform_group_sum` check the corresponding coefficient identities for products of forms.

- `GenericCubicHessianPullback.hessian_rank_eq_six` and `ThreeHeadPoleHessian.mixed_independent_cubic_ne_oriented` check the exact Hessian-rank obstruction, including all oriented competitors. `SymmetricCubicRecovery.eq_of_squarefree` checks exact recovery from squarefree data under the rank and cross-minor hypotheses.

- `ExplicitCubicRawObstruction.cubic_ne_oriented_with_readout` instantiates the exact raw obstruction with the displayed rational fourteen-variable target. `FiniteGridPole.explicit_bounded_pole_point` and `ExplicitCubicQuantitativeBounds.exists_pole_with_bounded_nonsingular_minor` check the quantitative finite point selection and target minor bound.

- `ExplicitCubicSquarefreeGap.squarefree_coefficient_gap_with_readout` checks the full uniform squarefree exclusion with its explicit radius. `ThreeHeadMeanGap.not_meanCleared_close` connects this exclusion to every admissible untied vanilla representation.

- `PureCubicInterpolation.coefficient_recovery` checks coefficient recovery from the actual finite rational zero chart, including its kernel, denominator bounds, and the existence and conditioning of the required minor. `PureCubicFiniteRigidity.finite_sign_rigidity` checks the complete finite-grid sign-rigidity argument for every nonzero real cubic.

- `ThreeHeadMeanSign.meanCleared_sign` and `ReplicatedMeanGrid.rawTarget_classifier_grid` connect the original Boolean cube, exact untied averaging, and the entire finite mean grid, including ties.

- `PureRoPEReplicationFive.explicit_sharedHStar_le_five` checks the improved five-head upper bound for the actual explicit function in the literal shared-embedding vanilla architecture.

All audited declarations use only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or new axiom is used. The original model, its admissibility conditions, and its head-count definitions have not been modified. The [certificate package](../../artifacts/rope/explicit_separation/README.md) gives the exact verification command, research manifest, unsuccessful approaches, and remaining questions.
